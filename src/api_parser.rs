// IDL parser. The IDL has one way to define a type (a prefix-free real
// struct/enum/handle) and one way to define an API (an `api <Domain>`
// direct-function block).

// Not every field and helper of the model is consumed yet; suppress dead-code
// noise rather than amputate the model.
#![allow(dead_code)]

use heck::ToSnakeCase;
use pest::iterators::Pair;
use pest::Parser;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Read;
use std::path::Path;

const _GRAMMAR: &str = include_str!("api.pest");

/// Primitive scalar type names the IDL understands directly. char maps to C
/// char, not a fixed-width int; usize/isize to C size_t/ptrdiff_t.
const PRIMITIVE_TYPES: &[&str] = &[
    "void", "char", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64", "bool", "f32", "f64",
    "usize", "isize",
];

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum VariableType {
    None,
    /// The self receiver of a method.
    SelfType,
    Enum,
    /// Struct / other named type.
    Regular,
    Str,
    Primitive,
    Reference,
}

#[derive(PartialEq, Debug, Clone, Default)]
pub enum ArrayType {
    /// Unsized array (pointer + length)
    #[default]
    Unsized,
    SizedArray(String),
}

/// One field / argument: name, type, and modifier flags.
#[derive(Debug, Clone)]
pub struct Variable {
    pub doc_comments: Vec<String>,
    pub def_file: String,
    pub name: String,
    pub vtype: VariableType,
    pub type_name: String,
    pub default_value: String,
    pub enum_type: EnumType,
    pub array: Option<ArrayType>,
    pub optional: bool,
    pub pointer: bool,
    pub const_pointer: bool,
    pub is_handle_type: bool,
    pub is_empty_struct: bool,
    /// true when this value's type is an extern opaque dependency: a
    /// pointer-only external type the generated code names verbatim (no Fl
    /// prefix) and never lays out by value. Set in [`second_pass`].
    pub is_extern_opaque: bool,
    /// The `#[view(<path>)]` on this value's extern opaque type, when it has
    /// one: the safe reference a consume-side wrapper takes. Set in
    /// [`second_pass`].
    pub opaque_view: Option<String>,
    /// true when this value's type is a `callback <Name>` construct - a named
    /// function-pointer typedef, not a by-value data struct. It crosses the API as
    /// the typedef itself (FlAppFrameFn). Set in [`second_pass`].
    pub is_callback: bool,
    /// Some when this field is an anonymous union { ... }. Holds the union's
    /// variant fields; name is the union field's name and type_name is unused.
    pub union_variants: Option<Vec<Variable>>,
    /// Some(T) when this api arg carries a `[slice(T)]` / `[slice_mut(T)]` marker:
    /// it is the data pointer of a (pointer, count) pair, and the Rust façade
    /// collapses it and the immediately-following count arg into a single `&[T]` /
    /// `&mut [T]` parameter. The arg keeps its raw pointer + count C / sys crossing;
    /// the marker steers the façade only.
    pub slice_elem: Option<String>,
    /// true for `[slice_mut(T)]` (a caller-writable `&mut [T]` out-buffer); false
    /// for the read-only `[slice(T)]`. Only meaningful when slice_elem is Some.
    pub slice_mut: bool,
    /// Some((T, N)) for an `[array(T, N)]` api arg: a `*const T` the callee reads
    /// exactly N of. The façade takes `&[T; N]`; the raw pointer C / sys crossing
    /// is unchanged.
    pub array_param: Option<(String, String)>,
    /// true when this api arg carries a bare `[transfer]` marker (service-consume
    /// wrapper): its owning newtype is moved into the callee (the wrapper hands C the
    /// raw pointer and forgets the newtype). The raw pointer crossing is unchanged.
    pub is_transfer: bool,
    /// Some when this value's type is a `#[attributes(Mirror)]` config struct:
    /// where its safe twin lives. The Rust façade takes the twin and lowers it at
    /// the call; the raw C / sys crossing is unchanged. Set in [`second_pass`].
    pub mirror: Option<MirrorRef>,
    /// `[from(<host name>)]`: the paired host field is named this instead of name.
    pub from_host: Option<String>,
    /// `[with(<helper path>)]`: a hand-written host helper marshals this field whole.
    pub with_helper: Option<String>,
    /// `[read_with(<helper path>)]`: the consume side reads this field through a
    /// hand-written helper instead of copying it.
    pub read_with: Option<String>,
    /// `[fixed(<value>)]`: the field has no host counterpart; every publish writes
    /// this value. The consume side still reads it.
    pub fixed: Option<String>,
}

/// The pairing annotations that precede one field, collected as they are parsed.
#[derive(Default)]
struct FieldAttrs {
    from_host: Option<String>,
    with_helper: Option<String>,
    read_with: Option<String>,
    fixed: Option<String>,
}

impl FieldAttrs {
    /// Take one annotation. A repeat is refused rather than silently keeping the
    /// last of them.
    fn absorb(&mut self, rule: Pair<Rule>) {
        let text = rule.as_str().to_owned();
        let (slot, value) = match rule.as_rule() {
            Rule::from_attr => (
                &mut self.from_host,
                ApiParser::first_child_str(rule, Rule::name),
            ),
            Rule::with_attr => (
                &mut self.with_helper,
                ApiParser::first_child_str(rule, Rule::path),
            ),
            Rule::read_with_attr => (
                &mut self.read_with,
                ApiParser::first_child_str(rule, Rule::path),
            ),
            Rule::fixed_attr => (
                &mut self.fixed,
                ApiParser::first_child_str(rule, Rule::name),
            ),
            other => unreachable!("not a field annotation: {:?}", other),
        };
        assert!(
            slot.is_none(),
            "api_gen: one `{}` per field, and this one repeats it",
            text
        );
        *slot = value;
    }
}

/// The host type a def type pairs with: `#[view(<path>)]`, plus the enum-only
/// `fallback = <variant>` arm a wrong value decodes to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ViewSpec {
    pub path: String,
    pub fallback: Option<String>,
}

/// The safe twin of a `#[attributes(Mirror)]` struct, as a referring value sees it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirrorRef {
    /// Façade module the twin is emitted into - the defining def's base filename.
    pub module: String,
    /// Whether the twin carries a borrow parameter (it has a &str or `Option<&T>`
    /// field), so a referring signature spells it `Name<'_>`.
    pub lifetime: bool,
}

impl Default for Variable {
    fn default() -> Self {
        Variable {
            name: String::new(),
            doc_comments: Vec::new(),
            def_file: String::new(),
            vtype: VariableType::None,
            type_name: String::new(),
            enum_type: EnumType::Regular,
            default_value: String::new(),
            array: None,
            optional: false,
            pointer: false,
            const_pointer: false,
            is_handle_type: false,
            is_empty_struct: false,
            is_extern_opaque: false,
            opaque_view: None,
            is_callback: false,
            union_variants: None,
            slice_elem: None,
            slice_mut: false,
            array_param: None,
            is_transfer: false,
            mirror: None,
            from_host: None,
            with_helper: None,
            read_with: None,
            fixed: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FunctionType {
    /// Method with a self receiver.
    Regular,
    /// Free function.
    Static,
    /// Manually implemented - api_gen emits only the declaration.
    Manual,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub doc_comments: Vec<String>,
    pub def_file: String,
    pub name: String,
    pub c_name: String,
    pub function_args: Vec<Variable>,
    pub return_val: Option<Variable>,
    pub func_type: FunctionType,
    /// true when the declaration ends in a C varargs marker (...). The body
    /// stays hand-written and the generator emits .. in the fn-pointer slot plus
    /// a call macro.
    pub has_varargs: bool,
    /// `[drop]`: this api slot is the RAII destructor of an opaque-handle domain.
    /// The Rust façade emits it as impl Drop (not an inherent method), and its
    /// sole `*void` arg names the handle every other slot in the block receives.
    /// C / sys output is unaffected.
    pub is_drop: bool,
    /// `[const]`: the generated RAII method takes &self rather than the default
    /// &mut self. Ignored outside the opaque-handle façade.
    pub is_const: bool,
    /// `[rename(<name>)]`: override the emitted Rust method name. The c_name keeps
    /// the original slot name, so C / sys output is unaffected.
    pub rename: Option<String>,
    /// `[scope_begin]`: this api slot opens a thread-local scope. The Rust façade
    /// emits it returning a `<Domain>Scope` guard whose Drop calls the paired
    /// `[scope_end]` slot. C / sys output is unaffected.
    pub is_scope_begin: bool,
    /// `[scope_end]`: the paired close of a `[scope_begin]` slot. The Rust façade
    /// calls its c_name from the guard's Drop, and still emits it as a normal
    /// method for explicit manual closing. C / sys output is unaffected.
    pub is_scope_end: bool,
    /// `[borrowed]`: the slot's String args lower to a borrowed FlString
    /// pointing straight at the caller's &str rather than the per-frame-arena copy.
    /// Only valid where the callee copies the bytes before returning. A String
    /// return stays a borrowed &str where a wrapper's &self anchors it, and is
    /// an owned copy on the receiverless façade. C / sys output is unaffected.
    pub is_borrowed: bool,
    /// `[c_only]`: every consumer of the slot is C, so the Rust binding and
    /// wrapper are not emitted. C prototype, call macro, and export entry are
    /// unchanged.
    pub is_c_only: bool,
    /// `[retained]`: the callee stores the slot's `*const T` pointer arg past the
    /// call, so the Rust façade must not pass the caller's borrow through. It copies
    /// the value into wrapper-owned static storage and hands C a pointer to that
    /// copy. In the service-consume wrapper the same marker instead demands a
    /// &'static T. C / sys unaffected.
    pub is_retained: bool,
    /// `[transfer(free = <slot>)]` on a slot's return (service-consume wrapper):
    /// the returned pointer's ownership crosses the ABI, so the wrapper emits an
    /// owning newtype whose Drop calls the named destroy slot. transfer_free
    /// holds that slot name. C / sys output is unaffected.
    pub is_transfer: bool,
    /// The destroy slot named by `[transfer(free = <slot>)]`; None for a bare
    /// `[transfer]` (which is a hard-fail on a return - the newtype needs a paired
    /// destroy slot). Only read by the service-consume wrapper emitter.
    pub transfer_free: Option<String>,
    /// `[status]` (service-consume wrapper): the slot's integer/bool status return
    /// maps to `Result<T, FlError>`, a trailing `*mut T` out-param becoming the
    /// Ok value. C / sys output is unaffected.
    pub is_status: bool,
    /// `[thread_safe]` (service-consume wrapper): this slot is safe to call from
    /// any thread. When a whole service is thread-safe the wrapper gains
    /// unsafe impl Send + Sync. C / sys output is unaffected.
    pub is_thread_safe: bool,
}

impl Default for Function {
    fn default() -> Self {
        Function {
            doc_comments: Vec::new(),
            name: String::new(),
            c_name: String::new(),
            def_file: String::new(),
            function_args: Vec::new(),
            return_val: None,
            func_type: FunctionType::Regular,
            has_varargs: false,
            is_drop: false,
            is_const: false,
            rename: None,
            is_scope_begin: false,
            is_scope_end: false,
            is_borrowed: false,
            is_c_only: false,
            is_retained: false,
            is_transfer: false,
            transfer_free: None,
            is_status: false,
            is_thread_safe: false,
        }
    }
}

/// An `api <Domain> { ... }` block: a domain of free functions (no self) bound
/// to hand-written `fl_<domain>_<fn>` bodies. c_gen emits the direct C prototypes
/// and the call macros that route to them.
#[derive(Debug, Default)]
pub struct Api {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub def_file: String,
    pub functions: Vec<Function>,
    /// `#[attributes(service)]`: this block's slots are named with the domain
    /// already baked in (arena_create), so their raw slot name is the exported
    /// C symbol - c_gen emits the plain prototypes (no `fl_<domain>_` re-prefix, no
    /// convenience macros) and the Rust FFI links them directly. It also gates the
    /// Rust façade off for every slot. false => the ordinary `fl_<domain>_<fn>`
    /// direct path.
    pub is_service: bool,
    /// `#[attributes(service, thread_safe)]`: the whole service is safe to call from
    /// any thread, so the generated wrapper gains unsafe impl Send + Sync. false
    /// => the wrapper is !Send + !Sync unless every generated slot is individually
    /// `[thread_safe]`.
    pub is_thread_safe: bool,
}

/// A `callback <Name>(args) -> ret` construct: a named C function-pointer typedef
/// for a fn-pointer used as an argument or struct-field type. c_gen emits
/// `typedef ret (*Fl<Name>)(args);`; rust_gen emits the matching nullable
/// fn-pointer alias. The args are ordinary named variables (no implicit self).
#[derive(Debug, Default, Clone)]
pub struct Callback {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub def_file: String,
    pub function_args: Vec<Variable>,
    pub return_val: Option<Variable>,
}

/// Marks a struct as a handle: an opaque integer the toolkit hands out
/// (`#[handle(u32, invalid = 0xFFFFFFFF)]`). int_type is the underlying integer
/// width (an IDL primitive like u32 / u64); invalid is the sentinel value
/// the generator emits as a `#define`.
#[derive(Debug, Clone)]
pub struct HandleSpec {
    pub int_type: String,
    pub invalid: String,
}

/// One field of a struct, in authored order - a reference into either
/// [`Struct::variables`] or [`Struct::functions`] by index. The .def may
/// interleave value fields and function-fields, and the generated C/Rust layout
/// must preserve that order to stay byte-identical to the hand-written struct.
#[derive(Debug, Clone, Copy)]
pub enum FieldRef {
    Var(usize),
    Func(usize),
}

/// A struct definition (plain, handle, or opaque).
#[derive(Debug, Default)]
pub struct Struct {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub def_file: String,
    pub variables: Vec<Variable>,
    pub functions: Vec<Function>,
    /// Value + function fields in authored .def order (see [`FieldRef`]). Built
    /// by the parser; empty for structs constructed directly (e.g. in tests), in
    /// which case [`Struct::ordered_fields`] falls back to variables-then-functions.
    pub field_order: Vec<FieldRef>,
    pub attributes: Vec<String>,
    pub is_handle_type: bool,
    /// Some when the struct carries a `#[handle(...)]` annotation: the underlying
    /// integer width + invalid sentinel value.
    pub handle: Option<HandleSpec>,
    /// `#[view(<path>)]`: the host type this struct pairs with, when the
    /// `<DefPrefix><Name>` -> `<Name>View` convention does not hold.
    pub view: Option<ViewSpec>,
    /// `#[read]`: emit a consume-side reader for this record and everything it
    /// nests.
    pub read: bool,
    /// `#[read(<Name>)]`: the owned type the reader answers, when the convention
    /// would build an unusable name.
    pub read_owned: Option<String>,
}

/// The variant a plain enum values zero, following C's sequential numbering: an
/// unvalued entry is one past the one before it. A value the parser cannot read as
/// a literal makes it and everything numbered from it unknown rather than assumed.
pub fn zero_variant(edef: &Enum) -> Option<&str> {
    let mut next = Some(0i64);
    for entry in &edef.entries {
        let value = match &entry.value {
            EnumValue::Value(v) => literal_value(v),
            EnumValue::None => next,
            EnumValue::OrList(_) => None,
        };
        if value == Some(0) {
            return Some(&entry.name);
        }
        next = value.map(|v| v + 1);
    }
    None
}

/// A def-spelled enum value as a number: decimal, or C's 0x hex.
fn literal_value(raw: &str) -> Option<i64> {
    let raw = raw.trim();
    match raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
        Some(hex) => i64::from_str_radix(hex, 16).ok(),
        None => raw.parse().ok(),
    }
}

impl Struct {
    /// Fields in authored order, interleaving value and function fields. Falls back
    /// to all variables then all functions when field_order is empty (a struct
    /// built without the parser).
    pub fn ordered_fields(&self) -> Vec<FieldRef> {
        if self.field_order.is_empty() {
            self.variables
                .iter()
                .enumerate()
                .map(|(i, _)| FieldRef::Var(i))
                .chain((0..self.functions.len()).map(FieldRef::Func))
                .collect()
        } else {
            self.field_order.clone()
        }
    }
}

/// The flavor of an `extern <kind> <Name>` declaration. Only Opaque exists; an
/// `#include`-of-a-public-header dependency is named per-file by a `mod <name>`
/// directive instead (see [`ApiDef::mods`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternKind {
    /// `extern opaque <Name>` - a forward declaration only, for a pointer-only
    /// dependency the generated header never dereferences.
    Opaque,
}

/// An `extern <kind> <Name>` declaration: a type the IDL references but does not
/// define. name is the verbatim external C type (no Fl prefix applied).
#[derive(Debug, Clone)]
pub struct ExternType {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub kind: ExternKind,
    /// `#[view(<path>)]`: the safe reference type a consume-side wrapper takes
    /// in place of a pointer to this type.
    pub view: Option<String>,
}

#[derive(Debug)]
pub enum EnumValue {
    None,
    Value(String),
    OrList(Vec<String>),
}

#[derive(Debug)]
pub struct EnumEntry {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub value: EnumValue,
    /// `[from(<host variant>)]`: the paired host variant is named this.
    pub from_host: Option<String>,
}

/// Whether an enum is a plain sequential enum or a bitflags set.
#[derive(Clone, Copy, Debug, PartialEq, Default)]
pub enum EnumType {
    #[default]
    Regular,
    Bitflags,
}

#[derive(Debug, Default)]
pub struct Enum {
    pub doc_comments: Vec<String>,
    pub name: String,
    pub def_file: String,
    pub enum_type: EnumType,
    pub entries: Vec<EnumEntry>,
    /// `#[attributes(packed)]`: the C enum is __attribute__((packed)) (1 byte,
    /// like RP_PACKED_ENUM). Drives `#[repr(u8)]` and the size-1 layout.
    pub is_packed: bool,
    /// `#[attributes(error_enum)]`: this status enum also emits the shared
    /// FlError Rust error enum - one variant per non-success code plus an
    /// Unknown(i32) catch-all - with its decode impls, into the same generated
    /// module. Rust-side only; the C surface keeps the plain status enum.
    pub is_error_enum: bool,
    /// `#[attributes(serde)]`: the Rust enum also derives Serialize/Deserialize
    /// under the consuming crate's serde feature. For a type a host view carries
    /// by value, so a serialized fixture of that view can name the variant.
    pub is_serde: bool,
    /// `#[enumerators(<Stem>)]`: the C enumerator prefix stem. None falls back
    /// to [`name`], the common case (Key -> FlKey_A). Set only when the type
    /// name and constant prefix diverge (MouseEventType -> FlMouseEvent_Move).
    /// C-side only; Rust namespaces variants under the type.
    pub enumerator_override: Option<String>,
    /// `#[view(<path>, fallback = <variant>)]`: the host enum this one pairs with.
    pub view: Option<ViewSpec>,
}

/// Everything parsed out of one .def file.
#[derive(Debug, Default)]
pub struct ApiDef {
    /// Full path of the source file.
    pub filename: String,
    /// some_name for path/some_name.def.
    pub base_filename: String,
    pub structs: Vec<Struct>,
    pub enums: Vec<Enum>,
    /// `api <Domain> { ... }` direct-function blocks.
    pub apis: Vec<Api>,
    /// `extern opaque <Name>` declarations: pointer-only deps the generated header
    /// forward-declares but never defines.
    pub externs: Vec<ExternType>,
    /// `callback <Name>(args) -> ret` constructs: named C function-pointer
    /// typedefs (and the matching Rust fn-pointer alias).
    pub callbacks: Vec<Callback>,
    /// The public module this def's generated C header lands in
    /// (`flowi/include/flowi/<module>/`, cross-included as `<flowi/<module>/x.h>`).
    /// Set by a top-level `#[module(<name>)]` directive; defaults to ui when
    /// absent.
    pub module: String,
    /// `mod <name>` directives: hand-written public headers in this def's module
    /// that it depends on. The C header `#include`s each as
    /// `<flowi/<module>/<name>.h>` and the Rust binding emits `use crate::<name>::*;`.
    /// A type one of them defines is named by its IDL name like any other, and
    /// api_gen emits no body for it - the mod `#include` supplies the definition.
    pub mods: Vec<String>,
    /// `#[views(<host module path>)]`: the host module this def's types pair with
    /// by convention (`<DefPrefix><Name>` -> `<path>::<Name>View`).
    pub views: Option<String>,
    /// `#[reads(<plugin module path>)]`: the consume-side module this def's types
    /// are read back into (`<DefPrefix><Name>` -> `<path>::<Name>`).
    pub reads: Option<String>,
    /// `#[const(<NAME> = <value>)]` directives: cross-language constants emitted as
    /// a Rust pub const and a C `#define` from this single source.
    pub consts: Vec<(String, String)>,
}

impl ApiDef {
    /// Whether this def authors any C type api_gen emits into the real-type header
    /// (`flowi/<module>/<name>.h`): a plain real struct, a handle (integer typedef +
    /// sentinel), an opaque forward-decl, or a real enum.
    pub fn has_real_types(&self) -> bool {
        self.structs.iter().any(Struct::emits_typedef_header)
            || self.enums.iter().any(Enum::is_real_type)
    }

    /// Whether this def authors any `api <Domain>` block - it then emits the direct
    /// `fl_<domain>_<fn>` prototypes (or, for a `#[attributes(service)]` block, the
    /// raw-named exported prototypes) plus the call macros that route to them.
    pub fn has_apis(&self) -> bool {
        !self.apis.is_empty()
    }

    /// Whether this def authors any `callback <Name>` construct - a def of callbacks
    /// alone still produces a C header.
    pub fn has_callbacks(&self) -> bool {
        !self.callbacks.is_empty()
    }

    /// Whether any api block in this def is `#[attributes(service)]`: its slots
    /// are named with the domain already baked in (arena_create), so the exported C
    /// symbol is the raw slot name rather than a second `fl_<domain>_` re-prefix.
    pub fn is_service(&self) -> bool {
        self.apis.iter().any(|a| a.is_service)
    }
}

pub(crate) fn is_primitive(name: &str) -> bool {
    PRIMITIVE_TYPES.contains(&name)
}

#[derive(Parser)]
#[grammar = "api.pest"]
pub struct ApiParser;

impl ApiParser {
    /// Strip a doc-comment line's /// marker and the single space the IDL
    /// conventionally puts after it. A bare /// (an empty line inside a
    /// multi-paragraph block) is accepted.
    fn strip_doc_marker(s: &str) -> String {
        let body = s.strip_prefix("///").unwrap_or(s);
        body.strip_prefix(' ').unwrap_or(body).to_owned()
    }

    /// The string of pair's first child matching rule, if any - the shared
    /// spelling for one-value markers that wrap a single meaningful token.
    fn first_child_str(pair: Pair<Rule>, rule: Rule) -> Option<String> {
        pair.into_inner()
            .find(|e| e.as_rule() == rule)
            .map(|e| e.as_str().to_owned())
    }

    /// One entry per mechanical offender that never legitimately appears in a `.def`
    /// comment, `///` or plain `//` alike: issue refs, ADR refs, source-file pointers,
    /// and the generator-meta phrase. Empty means the buffer is clean.
    fn comment_policy_violations(buffer: &str) -> Vec<String> {
        let mut violations = Vec::new();
        for (i, line) in buffer.lines().enumerate() {
            // Scan from the first `//` on the line, not the line start, so a trailing
            // comment is caught too.
            let Some(start) = line.find("//") else {
                continue;
            };
            let trimmed = line[start..].trim_end();
            let lineno = i + 1;
            if trimmed
                .as_bytes()
                .windows(2)
                .any(|w| w[0] == b'#' && w[1].is_ascii_digit())
            {
                violations.push(format!(
                    "  line {lineno}: issue reference (`#NNN`): {trimmed}"
                ));
            }
            if trimmed.contains("ADR") {
                violations.push(format!("  line {lineno}: ADR reference: {trimmed}"));
            }
            if trimmed.contains(".def)") || trimmed.contains(".h)") {
                violations.push(format!("  line {lineno}: source-file pointer: {trimmed}"));
            }
            if trimmed
                .to_ascii_lowercase()
                .contains("exposed to rust through the generated direct api")
            {
                violations.push(format!("  line {lineno}: generator-meta phrase: {trimmed}"));
            }
        }

        violations
    }

    /// Fail generation when the buffer trips [`Self::comment_policy_violations`].
    fn validate_comment_policy(buffer: &str, filename: &str) {
        let violations = Self::comment_policy_violations(buffer);
        if !violations.is_empty() {
            panic!(
                "api_gen: comment policy violation(s) in {} (ADR-0044 — a `.def` comment \
                 names no issue, ADR or source file; move rationale to an ADR):\n{}",
                filename,
                violations.join("\n")
            );
        }
    }

    pub fn parse_file<P: AsRef<Path>>(path: P, api_def: &mut ApiDef) {
        let mut buffer = String::new();
        let pathname = path.as_ref().to_str().unwrap();

        let mut f = File::open(pathname)
            .unwrap_or_else(|e| panic!("ApiParser: Unable to open {}: {}", pathname, e));
        f.read_to_string(&mut buffer)
            .unwrap_or_else(|e| panic!("ApiParser: Unable to read from {}: {}", pathname, e));

        Self::parse_string(&buffer, pathname, api_def);
    }

    pub fn parse_string(buffer: &str, filename: &str, api_def: &mut ApiDef) {
        Self::validate_comment_policy(buffer, filename);

        let chunks = ApiParser::parse(Rule::chunk, buffer)
            .unwrap_or_else(|e| panic!("ApiParser: {} {}", filename, e));

        let base_filename = Path::new(filename).file_name().unwrap().to_str().unwrap();
        let base_filename = &base_filename[..base_filename.len() - 4];
        let mut current_comments = Vec::new();

        api_def.filename = filename.to_owned();
        api_def.base_filename = base_filename.to_owned();
        // Default module; a top-level `#[module(<name>)]` directive overrides it.
        api_def.module = "ui".to_owned();

        for chunk in chunks {
            match chunk.as_rule() {
                Rule::moduledef => {
                    for entry in chunk.into_inner() {
                        if entry.as_rule() == Rule::name {
                            api_def.module = entry.as_str().to_owned();
                        }
                    }
                }

                Rule::viewsdef => {
                    api_def.views = Self::first_child_str(chunk, Rule::path);
                }

                Rule::readsdef => {
                    api_def.reads = Self::first_child_str(chunk, Rule::path);
                }

                Rule::moddef => {
                    for entry in chunk.into_inner() {
                        if entry.as_rule() == Rule::name {
                            api_def.mods.push(entry.as_str().to_owned());
                        }
                    }
                }

                Rule::constdef => {
                    let mut inner = chunk.into_inner();
                    let name = inner.next().expect("const name").as_str().to_owned();
                    let value = inner.next().expect("const value").as_str().to_owned();
                    api_def.consts.push((name, value));
                }

                Rule::structdef => {
                    let sdef = Self::fill_struct(chunk, &current_comments, &api_def.base_filename);
                    current_comments.clear();
                    api_def.structs.push(sdef);
                }

                Rule::doc_comment => {
                    current_comments.push(Self::strip_doc_marker(chunk.as_str()));
                }

                Rule::apidef => {
                    let api = Self::fill_api(chunk, &current_comments, &api_def.base_filename);
                    current_comments.clear();
                    api_def.apis.push(api);
                }

                Rule::externdef => {
                    let ext = Self::fill_extern(chunk, &current_comments);
                    current_comments.clear();
                    api_def.externs.push(ext);
                }

                Rule::callbackdef => {
                    let cb = Self::fill_callback(chunk, &current_comments, &api_def.base_filename);
                    current_comments.clear();
                    api_def.callbacks.push(cb);
                }

                Rule::enumdef => {
                    let mut enum_def = Enum {
                        def_file: base_filename.to_owned(),
                        doc_comments: current_comments.to_owned(),
                        ..Default::default()
                    };
                    current_comments.clear();

                    let mut attributes = Vec::new();

                    for entry in chunk.into_inner() {
                        match entry.as_rule() {
                            Rule::name => enum_def.name = entry.as_str().to_owned(),
                            Rule::attributes => attributes = Self::get_attributes(entry),
                            Rule::enum_prefix => {
                                enum_def.enumerator_override =
                                    Self::first_child_str(entry, Rule::name);
                            }
                            Rule::view_attr => enum_def.view = Some(Self::get_view_attr(entry)),
                            Rule::fieldlist => enum_def.entries = Self::fill_field_list_enum(entry),
                            _ => (),
                        }
                    }

                    enum_def.enum_type = Self::determine_enum_type(&attributes);
                    enum_def.is_packed = attributes.iter().any(|a| a == "packed");
                    enum_def.is_error_enum = attributes.iter().any(|a| a == "error_enum");
                    enum_def.is_serde = attributes.iter().any(|a| a == "serde");
                    api_def.enums.push(enum_def);
                }

                _ => (),
            }
        }
    }

    fn determine_enum_type(attributes: &[String]) -> EnumType {
        if attributes.iter().any(|t| t == "bitflags") {
            EnumType::Bitflags
        } else {
            EnumType::Regular
        }
    }

    fn fill_struct(chunk: Pair<Rule>, doc_comments: &[String], def_file: &str) -> Struct {
        let mut sdef = Struct {
            doc_comments: doc_comments.to_owned(),
            def_file: def_file.to_owned(),
            ..Default::default()
        };

        for entry in chunk.into_inner() {
            match entry.as_rule() {
                Rule::name => sdef.name = entry.as_str().to_owned(),
                Rule::attributes => sdef.attributes = Self::get_attributes(entry),
                Rule::handle => sdef.handle = Some(Self::get_handle(entry)),
                Rule::view_attr => sdef.view = Some(Self::get_view_attr(entry)),
                Rule::read_attr => {
                    sdef.read = true;
                    sdef.read_owned = Self::first_child_str(entry, Rule::name);
                }
                Rule::fieldlist => {
                    let (var_entries, func_entries, field_order) = Self::fill_field_list(entry);
                    sdef.variables = var_entries;
                    sdef.functions = func_entries;
                    sdef.field_order = field_order;
                }
                _ => (),
            }
        }

        if sdef.view.as_ref().is_some_and(|v| v.fallback.is_some()) {
            panic!(
                "api_gen: `fallback` is an enum arm, not a struct one: drop it from `{}`",
                sdef.name
            );
        }

        sdef.is_handle_type = sdef.handle.is_some() || sdef.has_attribute("Handle");
        sdef
    }

    /// Parse a `#[handle(u32, invalid = 0xFFFFFFFF)]` annotation.
    fn get_handle(rule: Pair<Rule>) -> HandleSpec {
        let mut int_type = String::new();
        let mut invalid = String::new();

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::vtype => int_type = entry.as_str().to_owned(),
                Rule::name_or_num => invalid = entry.as_str().to_owned(),
                _ => (),
            }
        }

        HandleSpec { int_type, invalid }
    }

    /// `[from(...)]` / `[with(...)]` / `[read_with(...)]` / `[fixed(...)]` pair a
    /// value field with a host one. On a union or a function-pointer field they
    /// would silently mean nothing, so they are refused.
    fn reject_pairing_attrs(attrs: &FieldAttrs, name: &str) {
        if attrs.from_host.is_some()
            || attrs.with_helper.is_some()
            || attrs.read_with.is_some()
            || attrs.fixed.is_some()
        {
            panic!(
                "api_gen: pairing annotations apply to value fields only: drop them from `{}`",
                name
            );
        }
    }

    /// Parse a `#[view(<path>)]` / `#[view(<path>, fallback = <variant>)]` annotation.
    fn get_view_attr(rule: Pair<Rule>) -> ViewSpec {
        let mut path = String::new();
        let mut fallback = None;

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::path => path = entry.as_str().to_owned(),
                Rule::name => fallback = Some(entry.as_str().to_owned()),
                _ => (),
            }
        }

        ViewSpec { path, fallback }
    }

    /// The namelist inside `#[attributes(...)]`.
    fn get_attributes(rule: Pair<Rule>) -> Vec<String> {
        let mut attribs = Vec::new();
        for entry in rule.into_inner() {
            if entry.as_rule() == Rule::namelist {
                attribs = Self::get_namelist_list(entry);
            }
        }
        attribs
    }

    fn get_namelist_list(rule: Pair<Rule>) -> Vec<String> {
        rule.into_inner().map(|e| e.as_str().to_owned()).collect()
    }

    fn fill_field_list(rule: Pair<Rule>) -> (Vec<Variable>, Vec<Function>, Vec<FieldRef>) {
        let mut var_entries = Vec::new();
        let mut func_entries = Vec::new();
        let mut field_order = Vec::new();
        let mut doc_comments = Vec::new();

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::field => {
                    // The pairing attributes precede the field they annotate.
                    let mut attrs = FieldAttrs::default();

                    for field in entry.into_inner() {
                        match field.as_rule() {
                            Rule::from_attr
                            | Rule::with_attr
                            | Rule::read_with_attr
                            | Rule::fixed_attr => attrs.absorb(field),
                            Rule::union_field => {
                                let var = Self::get_union_field(field, &doc_comments);
                                Self::reject_pairing_attrs(&attrs, &var.name);
                                field_order.push(FieldRef::Var(var_entries.len()));
                                var_entries.push(var);
                                doc_comments.clear();
                            }
                            Rule::var => {
                                let mut var = Self::get_variable(field, &doc_comments);
                                var.from_host = attrs.from_host.take();
                                var.with_helper = attrs.with_helper.take();
                                var.read_with = attrs.read_with.take();
                                var.fixed = attrs.fixed.take();
                                field_order.push(FieldRef::Var(var_entries.len()));
                                var_entries.push(var);
                                doc_comments.clear();
                            }
                            Rule::function => {
                                let func = Self::get_function(field, &doc_comments);
                                Self::reject_pairing_attrs(&attrs, &func.name);
                                field_order.push(FieldRef::Func(func_entries.len()));
                                func_entries.push(func);
                                doc_comments.clear();
                            }
                            _ => (),
                        }
                    }
                }

                Rule::doc_comment => {
                    doc_comments.push(Self::strip_doc_marker(entry.as_str()));
                }

                _ => (),
            }
        }

        (var_entries, func_entries, field_order)
    }

    /// Parse an anonymous name: union { variant: Type, ... } field. Variants are
    /// ordinary variables.
    fn get_union_field(rule: Pair<Rule>, doc_comments: &[String]) -> Variable {
        let mut var = Variable {
            doc_comments: doc_comments.to_owned(),
            vtype: VariableType::Regular,
            ..Variable::default()
        };
        let mut variants = Vec::new();

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::name => var.name = entry.as_str().to_owned(),
                Rule::varlist => {
                    for v in entry.into_inner() {
                        if v.as_rule() == Rule::var {
                            variants.push(Self::get_variable(v, &[]));
                        }
                    }
                }
                _ => (),
            }
        }

        var.union_variants = Some(variants);
        var
    }

    fn get_function(rule: Pair<Rule>, doc_comments: &[String]) -> Function {
        let mut function = Function {
            doc_comments: doc_comments.to_owned(),
            ..Function::default()
        };

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::name => function.name = entry.as_str().to_owned(),
                Rule::static_typ => function.func_type = FunctionType::Static,
                Rule::manual_typ => function.func_type = FunctionType::Manual,
                Rule::varlist => function.function_args = Self::get_variable_list(entry),
                Rule::retexp => function.return_val = Some(Self::get_variable(entry, &[])),
                _ => (),
            }
        }

        // Methods always carry an implicit leading self.
        if function.function_args.is_empty() {
            function.function_args.push(Variable {
                name: "self".to_owned(),
                vtype: VariableType::SelfType,
                type_name: "self".to_owned(),
                ..Variable::default()
            });
        }

        function
    }

    /// Fill an `extern opaque <Name>` declaration. The grammar only admits the
    /// opaque kind today, so the parsed kind is always Opaque.
    fn fill_extern(chunk: Pair<Rule>, doc_comments: &[String]) -> ExternType {
        let mut name = String::new();
        let mut view = None;
        for entry in chunk.into_inner() {
            match entry.as_rule() {
                Rule::name => name = entry.as_str().to_owned(),
                Rule::view_attr => view = Some(Self::get_view_attr(entry).path),
                _ => (),
            }
        }
        ExternType {
            doc_comments: doc_comments.to_owned(),
            name,
            kind: ExternKind::Opaque,
            view,
        }
    }

    /// Fill a `callback <Name>(args) -> ret` construct: its name, named args (no
    /// implicit self), and optional return. The arg/return type kinds resolve
    /// cross-file in [`second_pass`].
    fn fill_callback(chunk: Pair<Rule>, doc_comments: &[String], def_file: &str) -> Callback {
        let mut cb = Callback {
            doc_comments: doc_comments.to_owned(),
            def_file: def_file.to_owned(),
            ..Default::default()
        };

        for entry in chunk.into_inner() {
            match entry.as_rule() {
                Rule::name => cb.name = entry.as_str().to_owned(),
                // Plain named variables - no implicit self receiver, unlike a
                // struct method's varlist.
                Rule::varlist => {
                    for arg in entry.into_inner() {
                        cb.function_args.push(Self::get_variable(arg, &[]));
                    }
                }
                Rule::retexp => cb.return_val = Some(Self::get_variable(entry, &[])),
                _ => (),
            }
        }

        cb
    }

    fn fill_api(chunk: Pair<Rule>, doc_comments: &[String], def_file: &str) -> Api {
        let mut api = Api {
            doc_comments: doc_comments.to_owned(),
            def_file: def_file.to_owned(),
            ..Default::default()
        };

        for entry in chunk.into_inner() {
            match entry.as_rule() {
                Rule::name => api.name = entry.as_str().to_owned(),
                Rule::attributes => {
                    let attrs = Self::get_attributes(entry);
                    api.is_service = attrs.iter().any(|a| a == "service");
                    api.is_thread_safe = attrs.iter().any(|a| a == "thread_safe");
                }
                Rule::apifnlist => api.functions = Self::fill_api_fn_list(entry),
                _ => (),
            }
        }

        api
    }

    /// Parse the function list inside an api block, threading doc comments onto
    /// the following function. Unlike struct methods, api functions are free
    /// functions and take no implicit self.
    fn fill_api_fn_list(rule: Pair<Rule>) -> Vec<Function> {
        let mut functions = Vec::new();
        let mut doc_comments = Vec::new();

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::doc_comment => doc_comments.push(Self::strip_doc_marker(entry.as_str())),
                Rule::apifn => {
                    functions.push(Self::get_api_function(entry, &doc_comments));
                    doc_comments.clear();
                }
                _ => (),
            }
        }

        functions
    }

    /// Parse one api free function (`name(args) -> ret`). No implicit self; a
    /// trailing ... sets has_varargs and is dropped from the explicit arg list.
    fn get_api_function(rule: Pair<Rule>, doc_comments: &[String]) -> Function {
        let mut function = Function {
            doc_comments: doc_comments.to_owned(),
            func_type: FunctionType::Static,
            ..Function::default()
        };

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::manual_typ => function.func_type = FunctionType::Manual,
                Rule::drop_typ => function.is_drop = true,
                Rule::const_typ => function.is_const = true,
                Rule::scope_begin_typ => function.is_scope_begin = true,
                Rule::scope_end_typ => function.is_scope_end = true,
                Rule::borrowed_typ => function.is_borrowed = true,
                Rule::retained_typ => function.is_retained = true,
                Rule::c_only_typ => function.is_c_only = true,
                // A bare `[transfer]` leaves transfer_free None - a hard-fail
                // the wrapper emitter reports.
                Rule::transfer_typ => {
                    function.is_transfer = true;
                    for arg in entry.into_inner() {
                        if arg.as_rule() == Rule::transfer_args {
                            for kv in arg.into_inner() {
                                let mut names = kv.into_inner();
                                let key = names.next().map(|e| e.as_str().to_owned());
                                let val = names.next().map(|e| e.as_str().to_owned());
                                if key.as_deref() == Some("free") {
                                    function.transfer_free = val;
                                }
                            }
                        }
                    }
                }
                Rule::status_typ => function.is_status = true,
                Rule::thread_safe_typ => function.is_thread_safe = true,
                Rule::rename_typ => {
                    function.rename = Self::first_child_str(entry, Rule::name);
                }
                Rule::name if function.name.is_empty() => function.name = entry.as_str().to_owned(),
                Rule::apiargs => {
                    // Each apiarg wraps one of the apiarg grammar alternatives.
                    for arg in entry.into_inner() {
                        let inner = match arg.into_inner().next() {
                            Some(p) => p,
                            None => continue,
                        };
                        match inner.as_rule() {
                            Rule::varargs => function.has_varargs = true,
                            Rule::slice_arg => {
                                let mut elem = String::new();
                                let mut is_mut = false;
                                let mut var = None;
                                for p in inner.into_inner() {
                                    match p.as_rule() {
                                        Rule::slice_typ => elem = Self::slice_elem_type(p),
                                        Rule::slice_mut_typ => {
                                            elem = Self::slice_elem_type(p);
                                            is_mut = true;
                                        }
                                        Rule::var => var = Some(Self::get_variable(p, &[])),
                                        _ => (),
                                    }
                                }
                                let mut v = var.expect("slice_arg always wraps a var");
                                v.slice_elem = Some(elem);
                                v.slice_mut = is_mut;
                                function.function_args.push(v);
                            }
                            Rule::array_arg => {
                                let mut elem = String::new();
                                let mut len = String::new();
                                let mut var = None;
                                for p in inner.into_inner() {
                                    match p.as_rule() {
                                        Rule::array_typ => {
                                            for t in p.into_inner() {
                                                match t.as_rule() {
                                                    Rule::vtype => elem = t.as_str().to_owned(),
                                                    Rule::name_or_num => {
                                                        len = t.as_str().to_owned()
                                                    }
                                                    _ => (),
                                                }
                                            }
                                        }
                                        Rule::var => var = Some(Self::get_variable(p, &[])),
                                        _ => (),
                                    }
                                }
                                let mut v = var.expect("array_arg always wraps a var");
                                if len.is_empty()
                                    || !len.bytes().all(|b| b.is_ascii_digit())
                                    || len.bytes().all(|b| b == b'0')
                                {
                                    panic!(
                                        "api_gen: `[array({}, {})]` on `{}`: the length must be a positive integer literal",
                                        elem, len, v.name
                                    );
                                }
                                if !v.const_pointer || v.type_name != elem || v.array.is_some() {
                                    panic!(
                                        "api_gen: `[array({}, {})]` arg `{}` must be spelled `{}: *const {}`",
                                        elem, len, v.name, v.name, elem
                                    );
                                }
                                v.array_param = Some((elem, len));
                                function.function_args.push(v);
                            }
                            Rule::transfer_arg => {
                                let mut var = None;
                                for p in inner.into_inner() {
                                    if p.as_rule() == Rule::var {
                                        var = Some(Self::get_variable(p, &[]));
                                    }
                                }
                                let mut v = var.expect("transfer_arg always wraps a var");
                                v.is_transfer = true;
                                function.function_args.push(v);
                            }
                            _ => function.function_args.push(Self::get_variable(inner, &[])),
                        }
                    }
                }
                Rule::retexp => function.return_val = Some(Self::get_variable(entry, &[])),
                _ => (),
            }
        }

        function
    }

    fn slice_elem_type(rule: Pair<Rule>) -> String {
        Self::first_child_str(rule, Rule::vtype).unwrap_or_default()
    }

    fn get_variable_list(rule: Pair<Rule>) -> Vec<Variable> {
        let mut variables = vec![Variable {
            name: "self".to_owned(),
            vtype: VariableType::SelfType,
            ..Variable::default()
        }];

        for entry in rule.into_inner() {
            variables.push(Self::get_variable(entry, &[]));
        }

        variables
    }

    fn get_default_value(var: &mut Variable, rule: Pair<Rule>) {
        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::name_or_num | Rule::string => {
                    var.default_value = entry.as_str().to_owned();
                    break;
                }
                _ => (),
            }
        }
    }

    fn get_variable(rule: Pair<Rule>, doc_comments: &[String]) -> Variable {
        let mut vtype = Rule::var;
        let mut var = Variable::default();
        let mut type_name = String::new();

        var.doc_comments = doc_comments.to_owned();

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::name => var.name = entry.as_str().to_owned(),
                Rule::refexp => vtype = Rule::refexp,
                Rule::pointer_exp => vtype = Rule::pointer_exp,
                Rule::const_ptr_exp => vtype = Rule::const_ptr_exp,
                Rule::optional => var.optional = true,
                Rule::vtype => type_name = entry.as_str().to_owned(),
                Rule::default_val => Self::get_default_value(&mut var, entry),

                Rule::array => {
                    var.array = Some(ArrayType::Unsized);
                    for entry in entry.into_inner() {
                        match entry.as_rule() {
                            Rule::vtype => type_name = entry.as_str().to_owned(),
                            Rule::refexp => vtype = Rule::refexp,
                            Rule::pointer_exp => vtype = Rule::pointer_exp,
                            Rule::const_ptr_exp => vtype = Rule::const_ptr_exp,
                            Rule::array_size => {
                                var.array = Some(ArrayType::SizedArray(
                                    entry.into_inner().as_str().to_owned(),
                                ));
                            }
                            _ => (),
                        }
                    }
                }

                _ => (),
            }
        }

        let var_type = match vtype {
            Rule::refexp => VariableType::Reference,
            _ => {
                if type_name == "String" {
                    VariableType::Str
                } else if is_primitive(&type_name) {
                    VariableType::Primitive
                } else {
                    VariableType::Regular
                }
            }
        };

        if vtype == Rule::pointer_exp {
            var.pointer = true;
        }
        if vtype == Rule::const_ptr_exp {
            var.const_pointer = true;
        }

        var.type_name = type_name;
        var.vtype = var_type;
        var
    }

    fn fill_field_list_enum(rule: Pair<Rule>) -> Vec<EnumEntry> {
        let mut entries = Vec::new();
        let mut doc_comments = Vec::new();
        let mut current_value = 0;

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::field => {
                    let mut attrs = FieldAttrs::default();

                    for field in entry.into_inner() {
                        match field.as_rule() {
                            Rule::from_attr
                            | Rule::with_attr
                            | Rule::read_with_attr
                            | Rule::fixed_attr => attrs.absorb(field),
                            Rule::enum_type => {
                                let mut item =
                                    Self::get_enum(&doc_comments, &mut current_value, field);
                                let hatch = attrs
                                    .with_helper
                                    .as_ref()
                                    .map(|path| format!("[with({})]", path))
                                    .or_else(|| {
                                        attrs
                                            .read_with
                                            .as_ref()
                                            .map(|path| format!("[read_with({})]", path))
                                    })
                                    .or_else(|| {
                                        attrs.fixed.as_ref().map(|v| format!("[fixed({})]", v))
                                    });
                                if let Some(hatch) = hatch {
                                    panic!(
                                        "api_gen: `{}` is a struct-field annotation, not an enum \
                                         one: drop it from `{}`",
                                        hatch, item.name
                                    );
                                }
                                item.from_host = attrs.from_host.take();
                                entries.push(item);
                                doc_comments.clear();
                            }
                            _ => (),
                        }
                    }
                }

                Rule::doc_comment => {
                    doc_comments.push(Self::strip_doc_marker(entry.as_str()));
                }

                _ => (),
            }
        }

        entries
    }

    fn get_enum(doc_comments: &[String], current_value: &mut u64, rule: Pair<Rule>) -> EnumEntry {
        let mut name = String::new();
        let mut value = EnumValue::None;

        for entry in rule.into_inner() {
            match entry.as_rule() {
                Rule::name => name = entry.as_str().to_owned(),
                Rule::enum_assign => value = Self::get_enum_assign(entry),
                _ => (),
            }
        }

        match value {
            EnumValue::None => {
                value = EnumValue::Value(current_value.to_string());
                *current_value += 1;
            }
            EnumValue::Value(ref v) => {
                // An explicit = N fixes this entry's value and reseeds the
                // running counter so the next auto-numbered entry continues at
                // N + 1 (C enum semantics). Decimal and hex reseed alike.
                if let Some(v) = parse_enum_literal(v) {
                    *current_value = v + 1;
                }
            }
            _ => (),
        }

        EnumEntry {
            doc_comments: doc_comments.to_owned(),
            name,
            value,
            from_host: None,
        }
    }

    fn get_enum_assign(rule: Pair<Rule>) -> EnumValue {
        let mut strings = Vec::new();

        for entry in rule.into_inner() {
            if entry.as_rule() == Rule::or_namelist {
                for e in entry.into_inner() {
                    if e.as_rule() == Rule::string_to_end {
                        strings.push(e.as_str().trim().to_owned());
                    }
                }
            }
        }

        if strings.len() == 1 {
            EnumValue::Value(strings[0].to_owned())
        } else {
            EnumValue::OrList(strings)
        }
    }

    /// Second pass: resolve cross-file type kinds (enum/handle/empty-struct) on
    /// function args/returns and assign each function its C name.
    pub fn second_pass(api_defs: &mut [ApiDef], naming: &crate::naming::Naming) {
        let mut enum_names = HashSet::new();
        let mut empty_structs = HashSet::new();
        let mut handle_types = HashSet::new();
        let mut extern_opaque = HashSet::new();
        let mut opaque_views: HashMap<String, String> = HashMap::new();
        let mut callback_names = HashSet::new();
        // `#[attributes(Mirror)]` struct -> the façade module its safe twin is emitted
        // into.
        let mut mirror_defs: Vec<(&Struct, &str)> = Vec::new();
        let mut enums_without_zero = HashSet::new();
        let mut opaque_structs = HashSet::new();

        for api_def in api_defs.iter() {
            for s in &api_def.structs {
                if s.is_handle_type {
                    handle_types.insert(s.name.to_owned());
                }
                if s.is_opaque() {
                    opaque_structs.insert(s.name.to_owned());
                }
                if s.variables.is_empty() && !s.is_handle_type {
                    empty_structs.insert(s.name.to_owned());
                }
                if s.is_mirror() {
                    mirror_defs.push((s, &api_def.base_filename));
                }
            }
            for e in &api_def.enums {
                enum_names.insert(e.name.to_owned());
                if e.enum_type == EnumType::Regular && !Self::enum_has_zero_value(e) {
                    enums_without_zero.insert(e.name.to_owned());
                }
            }
            for ext in &api_def.externs {
                if ext.kind == ExternKind::Opaque {
                    extern_opaque.insert(ext.name.to_owned());
                    if let Some(view) = &ext.view {
                        opaque_views.insert(ext.name.to_owned(), view.to_owned());
                    }
                }
            }
            for cb in &api_def.callbacks {
                callback_names.insert(cb.name.to_owned());
            }
        }

        let mirrors = Self::resolve_mirrors(&mirror_defs);

        for api_def in api_defs.iter_mut() {
            for s in &mut api_def.structs {
                // A struct value field typed by an extern opaque dep must spell
                // verbatim too, so flag it the same way as a function-field arg.
                for var in &mut s.variables {
                    if extern_opaque.contains(&var.type_name) {
                        var.is_extern_opaque = true;
                    }
                }
                // Must run after the extern opaque annotation above, which the
                // validation reads to reject a pointer to an uninhabited host type.
                if s.is_mirror() {
                    // A by-value field that is itself a mirrored config records its twin.
                    for var in &mut s.variables {
                        if !var.pointer && !var.const_pointer {
                            if let Some(nested) = mirrors.get(&var.type_name) {
                                var.mirror = Some(nested.clone());
                            }
                        }
                    }
                    Self::validate_mirror_struct(s, &enums_without_zero, &opaque_structs);
                }
                for func in &mut s.functions {
                    Self::reject_bare_sized_arrays(func);
                    func.c_name = naming.c_func(&s.name.to_snake_case(), &func.name);
                    Self::resolve_function_kinds(
                        func,
                        &enum_names,
                        &handle_types,
                        &empty_structs,
                        &extern_opaque,
                        &callback_names,
                    );
                }
            }
            // An `api <Domain>` block's free functions are spelled `fl_<domain>_<fn>`.
            // A `#[attributes(service)]` block is the exception: its slot name is
            // the exported C symbol, so no second `fl_<domain>_` re-prefix.
            for api in &mut api_def.apis {
                let is_service = api.is_service;
                for func in &mut api.functions {
                    Self::reject_bare_sized_arrays(func);
                    func.c_name = if is_service {
                        func.name.clone()
                    } else {
                        naming.c_api_func(&api.name.to_snake_case(), &func.name)
                    };
                    Self::resolve_function_kinds(
                        func,
                        &enum_names,
                        &handle_types,
                        &empty_structs,
                        &extern_opaque,
                        &callback_names,
                    );
                    // A slot arg typed by a `#[attributes(Mirror)]` struct records the
                    // façade module holding the safe twin.
                    for arg in &mut func.function_args {
                        if let Some(mirror) = mirrors.get(&arg.type_name) {
                            arg.mirror = Some(mirror.clone());
                        }
                    }
                }
            }
            // A callback's args/return resolve cross-file exactly like a function's;
            // callbacks have no C name to assign.
            for cb in &mut api_def.callbacks {
                Self::reject_sized_array_values(
                    &cb.name,
                    &cb.function_args,
                    cb.return_val.as_ref(),
                );
                Self::resolve_arg_ret_kinds(
                    &mut cb.function_args,
                    cb.return_val.as_mut(),
                    &enum_names,
                    &handle_types,
                    &empty_structs,
                    &extern_opaque,
                    &callback_names,
                );
            }
        }

        for api_def in api_defs.iter_mut() {
            for api in &mut api_def.apis {
                for func in &mut api.functions {
                    for arg in &mut func.function_args {
                        arg.opaque_view = opaque_views.get(&arg.type_name).cloned();
                    }
                }
            }
        }
    }

    /// Reject a bare sized array in a signature (param or return): Rust would pass
    /// `[T; N]` by value while C decays it to a pointer and drops const - an ABI
    /// mismatch nothing else diagnoses. Struct fields are fine.
    fn reject_bare_sized_arrays(func: &Function) {
        Self::reject_sized_array_values(&func.name, &func.function_args, func.return_val.as_ref());
    }

    fn reject_sized_array_values(owner: &str, args: &[Variable], ret: Option<&Variable>) {
        for var in args.iter().chain(ret) {
            if matches!(var.array, Some(ArrayType::SizedArray(_))) {
                panic!(
                    "api_gen: `{}`: sized-array value `{}` is ABI-broken in a signature \
                     (Rust passes `[T; N]` by value, C a decayed pointer); spell a read \
                     buffer `[array(T, N)] {}: *const T`",
                    owner, var.name, var.name
                );
            }
        }
    }

    /// Whether a mirrored struct's field lowers to a borrow on its own (&str for
    /// a string, `Option<&T>` for an optional pointer). A nested mirrored field
    /// borrows only transitively, which [`resolve_mirrors`] resolves.
    fn mirror_field_borrows(var: &Variable) -> bool {
        var.vtype == VariableType::Str || var.const_pointer
    }

    /// Resolve every `#[attributes(Mirror)]` struct into the [`MirrorRef`] a referring
    /// value needs: the façade module its twin is emitted into, and whether that twin
    /// carries a lifetime.
    ///
    /// The lifetime is transitive - a config borrows through a nested mirrored config
    /// that borrows - so this takes a fixpoint over the whole set rather than a
    /// per-struct scan. The iteration is monotone over a finite set, so it terminates.
    fn resolve_mirrors(mirror_defs: &[(&Struct, &str)]) -> HashMap<String, MirrorRef> {
        Self::reject_mirror_cycles(mirror_defs);

        let mut borrows: HashMap<&str, bool> = mirror_defs
            .iter()
            .map(|(sdef, _)| {
                (
                    sdef.name.as_str(),
                    sdef.variables.iter().any(Self::mirror_field_borrows),
                )
            })
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for (sdef, _) in mirror_defs {
                if borrows[sdef.name.as_str()] {
                    continue;
                }
                let nested_borrows = sdef.variables.iter().any(|var| {
                    !var.pointer
                        && !var.const_pointer
                        && borrows
                            .get(var.type_name.as_str())
                            .copied()
                            .unwrap_or(false)
                });
                if nested_borrows {
                    borrows.insert(sdef.name.as_str(), true);
                    changed = true;
                }
            }
        }

        mirror_defs
            .iter()
            .map(|(sdef, module)| {
                (
                    sdef.name.to_owned(),
                    MirrorRef {
                        module: (*module).to_owned(),
                        lifetime: borrows[sdef.name.as_str()],
                    },
                )
            })
            .collect()
    }

    /// Reject a mirrored config that contains itself, directly or through other
    /// mirrors, naming the cycle - otherwise it surfaces as a rustc "recursive type
    /// has infinite size" on generated code.
    fn reject_mirror_cycles(mirror_defs: &[(&Struct, &str)]) {
        let by_name: HashMap<&str, &Struct> = mirror_defs
            .iter()
            .map(|(sdef, _)| (sdef.name.as_str(), *sdef))
            .collect();
        // Depth-first with the active path as the cycle witness; done keeps the walk
        // linear in the number of fields across all mirrors.
        let mut done: HashSet<&str> = HashSet::new();
        for (root, _) in mirror_defs {
            let mut path: Vec<&str> = Vec::new();
            Self::walk_mirror_cycle(root, &by_name, &mut path, &mut done);
        }
    }

    fn walk_mirror_cycle<'a>(
        sdef: &'a Struct,
        by_name: &HashMap<&'a str, &'a Struct>,
        path: &mut Vec<&'a str>,
        done: &mut HashSet<&'a str>,
    ) {
        if done.contains(sdef.name.as_str()) {
            return;
        }
        if let Some(at) = path.iter().position(|n| *n == sdef.name) {
            panic!(
                "api_gen: `#[attributes(Mirror)]` struct `{}` contains itself by value \
                 ({} -> {}); a mirrored config cannot be recursive",
                sdef.name,
                path[at..].join(" -> "),
                sdef.name
            );
        }
        path.push(sdef.name.as_str());
        for var in &sdef.variables {
            if var.pointer || var.const_pointer {
                continue;
            }
            if let Some(nested) = by_name.get(var.type_name.as_str()) {
                Self::walk_mirror_cycle(nested, by_name, path, done);
            }
        }
        path.pop();
        done.insert(sdef.name.as_str());
    }

    /// Whether a plain enum declares a variant with the value 0. An enum that does
    /// not cannot appear by value in a mirrored config struct: the mirror's
    /// Default is the C zero value, and a zero bit pattern that names no variant
    /// is not a legal value of the Rust type.
    fn enum_has_zero_value(edef: &Enum) -> bool {
        zero_variant(edef).is_some()
    }

    /// Reject a `#[attributes(Mirror)]` struct whose fields have no safe spelling,
    /// with a diagnostic naming the field - the generator emits the mirror on the
    /// strength of this check.
    ///
    /// The shapes a mirrored field may take are the ones the emitter lowers: a scalar
    /// string, an optional const pointer, a mutable pointer to an opaque type, a
    /// nested mirrored config, and a plain by-value field.
    fn validate_mirror_struct(
        sdef: &Struct,
        enums_without_zero: &HashSet<String>,
        opaque_structs: &HashSet<String>,
    ) {
        let reject = |field: &str, why: &str| -> ! {
            panic!(
                "api_gen: `#[attributes(Mirror)]` struct `{}`: field `{}` {}",
                sdef.name, field, why
            )
        };
        if !sdef.functions.is_empty() {
            reject(
                &sdef.functions[0].name,
                "is a function field; a mirrored struct carries data only",
            );
        }
        for var in &sdef.variables {
            if var.union_variants.is_some() {
                reject(&var.name, "is a union; no safe mirror spelling exists");
            }
            if var.array.is_some() {
                reject(&var.name, "is an array; no safe mirror spelling exists");
            }
            if var.vtype == VariableType::Str {
                if var.pointer || var.const_pointer {
                    reject(
                        &var.name,
                        "is a string pointer; only a scalar string mirrors",
                    );
                }
                continue;
            }
            if var.const_pointer {
                if var.type_name == "void"
                    || var.is_extern_opaque
                    || opaque_structs.contains(&var.type_name)
                {
                    reject(
                        &var.name,
                        "is an untyped or opaque pointer; no safe reference to it exists",
                    );
                }
                if var.type_name == "char" {
                    // A `*const char` is a NUL-terminated C string, not a reference to
                    // one char, so the optional-pointer lowering (`Option<&c_char>`)
                    // would be safe but meaningless.
                    reject(
                        &var.name,
                        "is a `*const char` C string; mirror it as `String` or lower it \
                         by hand",
                    );
                }
                continue;
            }
            if var.pointer {
                // An `#[attributes(Opaque)]` pointee is the exception: it generates as
                // an uninhabited enum, so there is no safe &mut to spell the field
                // with. The twin passes the raw pointer through and defaults it to null.
                if !opaque_structs.contains(&var.type_name) {
                    reject(
                        &var.name,
                        "is a mutable pointer; a mirrored config is passed by value, so a \
                         caller-writable field has no meaning",
                    );
                }
                continue;
            }
            if enums_without_zero.contains(&var.type_name) {
                reject(
                    &var.name,
                    "is an enum with no 0-valued variant, so the C zero default the \
                     mirror's `Default` reproduces is not a legal value",
                );
            }
        }
    }

    /// Resolve a function's arg/return type kinds against the cross-file type
    /// sets: an enum arg becomes Enum, and a handle/empty-struct arg or return
    /// is flagged. Return values do not take the Enum kind (a returned enum is
    /// spelled like any named type).
    fn resolve_function_kinds(
        func: &mut Function,
        enum_names: &HashSet<String>,
        handle_types: &HashSet<String>,
        empty_structs: &HashSet<String>,
        extern_opaque: &HashSet<String>,
        callback_names: &HashSet<String>,
    ) {
        Self::resolve_arg_ret_kinds(
            &mut func.function_args,
            func.return_val.as_mut(),
            enum_names,
            handle_types,
            empty_structs,
            extern_opaque,
            callback_names,
        );
    }

    /// Resolve cross-file type kinds on a bare arg list + optional return - the
    /// shared core of [`resolve_function_kinds`], reused by callback constructs.
    fn resolve_arg_ret_kinds(
        args: &mut [Variable],
        ret: Option<&mut Variable>,
        enum_names: &HashSet<String>,
        handle_types: &HashSet<String>,
        empty_structs: &HashSet<String>,
        extern_opaque: &HashSet<String>,
        callback_names: &HashSet<String>,
    ) {
        for arg in args {
            if enum_names.contains(&arg.type_name) {
                arg.vtype = VariableType::Enum;
            }
            if callback_names.contains(&arg.type_name) {
                arg.is_callback = true;
            }
            if handle_types.contains(&arg.type_name) {
                arg.is_handle_type = true;
            }
            if empty_structs.contains(&arg.type_name) {
                arg.is_empty_struct = true;
            }
            if extern_opaque.contains(&arg.type_name) {
                arg.is_extern_opaque = true;
            }
        }

        if let Some(ret_var) = ret {
            if handle_types.contains(&ret_var.type_name) {
                ret_var.is_handle_type = true;
            }
            if empty_structs.contains(&ret_var.type_name) {
                ret_var.is_empty_struct = true;
            }
            if extern_opaque.contains(&ret_var.type_name) {
                ret_var.is_extern_opaque = true;
            }
        }
    }
}

impl Struct {
    pub fn has_attribute(&self, attrib: &str) -> bool {
        self.attributes.iter().any(|s| s == attrib)
    }

    /// An opaque struct (`#[attributes(Opaque)]`): api_gen emits only a
    /// forward-declaration; the real body lives in a hand-written internal header.
    /// Used behind a pointer, never laid out by value.
    pub fn is_opaque(&self) -> bool {
        self.has_attribute("Opaque")
    }

    /// A mirrored config struct (`#[attributes(Mirror)]`): besides the raw
    /// `#[repr(C)]` ABI mirror in flowi_sys, api_gen emits a safe twin in the
    /// ergonomic flowi crate - &str where the ABI struct carries an FlString,
    /// `Option<&T>` where it carries an optional pointer - and every generated
    /// façade slot taking this struct takes the safe twin instead, lowering it at
    /// the call. C-side emission is unaffected.
    pub fn is_mirror(&self) -> bool {
        self.has_attribute("Mirror")
    }

    /// Whether api_gen emits a C definition/declaration for this struct in the
    /// real-type header: a plain real typedef struct, a handle (integer typedef +
    /// sentinel), or an opaque forward-decl. Every struct the IDL defines is one of
    /// these.
    pub fn emits_typedef_header(&self) -> bool {
        true
    }

    /// A plain real data struct: api_gen owns a full typedef struct { ... }
    /// with a computed field layout. Excludes handles (an integer typedef) and
    /// opaque types (a forward-decl), which emit headers but have no field layout.
    pub fn is_real_type(&self) -> bool {
        !self.is_handle_type && !self.is_opaque()
    }
}

impl Enum {
    /// A real enum: api_gen owns its C definition and emits a real
    /// typedef enum. Every enum the IDL defines is real.
    pub fn is_real_type(&self) -> bool {
        true
    }

    /// The literal a generator prints for this entry's `= <value>`, or None
    /// when the entry has no value to emit.
    ///
    /// A plain [`EnumValue::Value`] is returned verbatim so its authored spelling
    /// survives (a hex literal stays hex, a bare name stays the name, which C
    /// accepts). An [`EnumValue::OrList`] (All = A | B) is resolved within this
    /// enum and emitted as the combined integer. [`EnumValue::None`] never survives
    /// parsing (auto-numbering fills it in).
    ///
    /// Returns Err when an or-list references an enumerator that is neither a
    /// literal nor a defined name in this enum, or when references form a cycle.
    pub fn entry_value_literal(&self, entry: &EnumEntry) -> Result<Option<String>, String> {
        match &entry.value {
            EnumValue::None => Ok(None),
            EnumValue::Value(v) => Ok(Some(v.clone())),
            EnumValue::OrList(names) => {
                let mut acc = 0u64;
                for name in names {
                    acc |= self.resolve_ref(name, &mut Vec::new())?;
                }
                Ok(Some(acc.to_string()))
            }
        }
    }

    /// Resolve a single or-list reference to its integer value: a numeric
    /// literal parses directly; otherwise it names another enumerator whose
    /// value is resolved recursively (a nested or-list ORs its own members).
    /// visiting tracks the active resolution chain to detect cycles.
    fn resolve_ref(&self, reference: &str, visiting: &mut Vec<String>) -> Result<u64, String> {
        if let Some(v) = parse_enum_literal(reference) {
            return Ok(v);
        }
        if visiting.iter().any(|n| n == reference) {
            return Err(format!(
                "enum `{}`: cyclic reference while resolving enumerator `{}`",
                self.name, reference
            ));
        }
        let entry = self
            .entries
            .iter()
            .find(|e| e.name == reference)
            .ok_or_else(|| {
                format!(
                    "enum `{}`: entry references undefined enumerator `{}`",
                    self.name, reference
                )
            })?;
        match &entry.value {
            EnumValue::None => Ok(0),
            EnumValue::Value(v) => {
                visiting.push(reference.to_owned());
                let resolved = self.resolve_ref(v, visiting);
                visiting.pop();
                resolved
            }
            EnumValue::OrList(names) => {
                visiting.push(reference.to_owned());
                let mut acc = 0u64;
                for name in names {
                    match self.resolve_ref(name, visiting) {
                        Ok(v) => acc |= v,
                        Err(e) => {
                            visiting.pop();
                            return Err(e);
                        }
                    }
                }
                visiting.pop();
                Ok(acc)
            }
        }
    }
}

/// C spelling for an IDL primitive scalar name (stdint widths, for deterministic
/// output). f32/f64/bool/void map to their C keywords; u32/i16/... map
/// to the matching `uint*_t`/`int*_t`.
pub fn c_primitive(type_name: &str) -> Cow<'_, str> {
    match type_name {
        "f32" => "float".into(),
        "f64" => "double".into(),
        "bool" => "bool".into(),
        "void" => "void".into(),
        "char" => "char".into(),
        "usize" => "size_t".into(),
        "isize" => "ptrdiff_t".into(),
        _ => {
            if let Some(width) = type_name.strip_prefix('u') {
                format!("uint{}_t", width).into()
            } else if let Some(width) = type_name.strip_prefix('i') {
                format!("int{}_t", width).into()
            } else {
                type_name.to_owned().into()
            }
        }
    }
}

/// Parse an enum-value literal to its numeric value for auto-number reseeding.
/// Accepts decimal (256) and hex (0x10 / 0X10); returns None for anything
/// the reseed can't interpret (a symbolic reference, or an out-of-range literal).
fn parse_enum_literal(v: &str) -> Option<u64> {
    let v = v.trim();
    if let Some(hex) = v.strip_prefix("0x").or_else(|| v.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).ok()
    } else {
        v.parse::<u64>().ok()
    }
}

impl Variable {
    pub fn get_c_primitive_type(&self) -> Cow<'_, str> {
        c_primitive(&self.type_name)
    }
}

/// Structs that own functions (and aren't context markers) - the set the
/// function/handle generators iterate. Sorted for deterministic output.
pub fn get_structs_with_functions(api_defs: &[ApiDef]) -> Vec<&Struct> {
    let mut data: Vec<&Struct> = api_defs
        .iter()
        .flat_map(|api_def| api_def.structs.iter())
        .filter(|s| !s.functions.is_empty())
        .collect();

    data.sort_by(|a, b| a.name.cmp(&b.name));
    data
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_ok() {
        assert!(is_primitive("i32"));
    }

    #[test]
    fn test_primitive_false() {
        assert!(!is_primitive("dummy"));
    }

    #[test]
    fn char_is_a_primitive() {
        assert!(is_primitive("char"));
        assert_eq!(c_primitive("char"), "char");
        assert_eq!(c_primitive("void"), "void");
        assert_eq!(c_primitive("u32"), "uint32_t");
    }

    #[test]
    fn handle_and_opaque_annotations_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[handle(u32, invalid = 0xFFFFFFFF)]\n\
             struct ImageHandle {}\n\
             #[attributes(Opaque)]\n\
             struct TextInputState {}",
            "image_handle.def",
            &mut api_def,
        );

        let handle = api_def
            .structs
            .iter()
            .find(|s| s.name == "ImageHandle")
            .expect("handle parsed");
        assert!(handle.is_handle_type, "#[handle(...)] sets is_handle_type");
        let spec = handle.handle.as_ref().expect("handle spec");
        assert_eq!(spec.int_type, "u32");
        assert_eq!(spec.invalid, "0xFFFFFFFF");
        assert!(handle.emits_typedef_header());
        assert!(!handle.is_real_type());

        let opaque = api_def
            .structs
            .iter()
            .find(|s| s.name == "TextInputState")
            .expect("opaque parsed");
        assert!(opaque.is_opaque(), "#[attributes(Opaque)] marks it opaque");
        assert!(opaque.emits_typedef_header());
        assert!(!opaque.is_real_type());
    }

    #[test]
    fn service_attribute_and_scope_markers_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Arena {}\n\
             struct TempArena { arena: *Arena, pos: u64 }\n\
             #[attributes(service)]\n\
             api Arena {\n\
                 arena_create(reserved_size: u64, file: *const char, line: i32) -> *Arena\n\
                 arena_alloc_raw(arena: *Arena, size: u64, alignment: u64) -> *void\n\
                 [scope_begin] arena_temp_begin(arena: *Arena) -> TempArena\n\
                 [scope_end] arena_temp_end(temp: TempArena)\n\
             }",
            "arena.def",
            &mut api_def,
        );

        assert!(
            api_def.is_service(),
            "#[attributes(service)] sets is_service"
        );
        assert!(api_def.apis[0].is_service);

        let funcs = &api_def.apis[0].functions;
        assert!(funcs[2].is_scope_begin);
        assert!(funcs[3].is_scope_end);

        let mut plain = ApiDef::default();
        ApiParser::parse_string(
            "api Cursor { set_visible(visible: bool) }",
            "cursor.def",
            &mut plain,
        );
        assert!(!plain.is_service());
        assert_eq!(
            plain.module, "ui",
            "non-service defs keep the default module"
        );
    }

    #[test]
    fn ownership_annotations_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Widget {}\n\
             #[attributes(service, thread_safe)]\n\
             api Blob {\n\
                 [transfer(free = widget_free)] widget_new(size: u64) -> *Widget\n\
                 widget_free([transfer] w: *Widget)\n\
                 [status] parse(text: String, out: *u64) -> i32\n\
                 [thread_safe] ping()\n\
             }",
            "blob.def",
            &mut api_def,
        );

        assert!(api_def.apis[0].is_service);
        assert!(
            api_def.apis[0].is_thread_safe,
            "the block `thread_safe` attribute threads onto the api"
        );

        let funcs = &api_def.apis[0].functions;
        assert!(funcs[0].is_transfer);
        assert_eq!(funcs[0].transfer_free.as_deref(), Some("widget_free"));
        assert!(
            funcs[1].function_args[0].is_transfer,
            "the param-level [transfer] marks the arg for move"
        );
        assert!(
            !funcs[1].is_transfer,
            "a param marker is not a return marker"
        );
        assert!(funcs[2].is_status);
        assert!(funcs[3].is_thread_safe);
    }

    /// A bare `[transfer]` on a return parses with no free slot - the wrapper
    /// emitter turns that into a hard-fail, but the parser records it faithfully.
    #[test]
    fn bare_transfer_return_has_no_free_slot() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Widget {}\n\
             #[attributes(service)]\n\
             api Blob { [transfer] widget_new() -> *Widget }",
            "blob.def",
            &mut api_def,
        );
        let f = &api_def.apis[0].functions[0];
        assert!(f.is_transfer);
        assert_eq!(f.transfer_free, None);
    }

    #[test]
    fn pointer_primitive_fields_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Span { text: *const char, blob: *const void, scratch: *void }",
            "span.def",
            &mut api_def,
        );
        let s = &api_def.structs[0];
        assert_eq!(s.variables[0].type_name, "char");
        assert!(s.variables[0].const_pointer && !s.variables[0].pointer);
        assert_eq!(s.variables[1].type_name, "void");
        assert!(s.variables[1].const_pointer);
        assert_eq!(s.variables[2].type_name, "void");
        assert!(s.variables[2].pointer && !s.variables[2].const_pointer);
        assert!(s
            .variables
            .iter()
            .all(|v| v.vtype == VariableType::Primitive));
    }

    #[test]
    fn def_classification_routes_domains() {
        let mut real = ApiDef::default();
        ApiParser::parse_string(
            "enum CursorShape { Arrow = 0, Hand = 1, }\n\
             #[attributes(Copy)]\nstruct Cursor { shape: CursorShape }",
            "cursor.def",
            &mut real,
        );
        assert!(real.has_real_types(), "a prefix-free type is a real type");
        assert!(!real.has_apis(), "this def authors no api block");

        let mut api = ApiDef::default();
        ApiParser::parse_string(
            "api Cursor { set_visible(visible: bool) }",
            "cursor.def",
            &mut api,
        );
        assert!(api.has_apis(), "an api block authors a direct API");
    }

    #[test]
    fn hex_enum_value_reseeds_auto_number_counter() {
        assert_eq!(parse_enum_literal("256"), Some(256));
        assert_eq!(parse_enum_literal("0x10"), Some(16));
        assert_eq!(parse_enum_literal("0X10"), Some(16));
        assert_eq!(parse_enum_literal("Foo"), None);

        let value_of = |entry: &EnumEntry| match &entry.value {
            EnumValue::Value(v) => v.clone(),
            other => panic!("expected a scalar enum value, got {other:?}"),
        };

        let mut hex_def = ApiDef::default();
        ApiParser::parse_string("enum Foo { A, B = 0x10, C, }", "foo.def", &mut hex_def);
        let foo = &hex_def.enums[0].entries;
        assert_eq!(value_of(&foo[0]), "0", "A auto-numbers from 0");
        assert_eq!(
            value_of(&foo[1]),
            "0x10",
            "B keeps its explicit hex literal"
        );
        assert_eq!(value_of(&foo[2]), "17", "C continues at hex_value + 1");

        let mut dec_def = ApiDef::default();
        ApiParser::parse_string(
            "enum RpKey { Space = 32, Escape = 256, Enter, }",
            "rpkey.def",
            &mut dec_def,
        );
        let keys = &dec_def.enums[0].entries;
        assert_eq!(value_of(&keys[1]), "256", "Escape keeps its decimal value");
        assert_eq!(value_of(&keys[2]), "257", "Enter continues at 256 + 1");

        let mut seq_def = ApiDef::default();
        ApiParser::parse_string(
            "enum Shape { Arrow = 0, Hand = 1, Beam, }",
            "shape.def",
            &mut seq_def,
        );
        let shapes = &seq_def.enums[0].entries;
        assert_eq!(value_of(&shapes[0]), "0");
        assert_eq!(value_of(&shapes[1]), "1");
        assert_eq!(
            value_of(&shapes[2]),
            "2",
            "sequential auto-number unaffected"
        );
    }

    #[test]
    fn api_block_parses_free_functions_and_varargs() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "/// Cursor control.\n\
             api Cursor {\n\
                 /// Request a shape.\n\
                 set(cursor: Cursor)\n\
                 get_requested() -> Cursor\n\
                 set_visible(visible: bool)\n\
                 get_visible() -> bool\n\
             }\n\
             api Format {\n\
                 frame_string(fmt: *const char, ...) -> String\n\
             }",
            "cursor.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        assert!(api_def.has_apis(), "the def authors api blocks");
        assert_eq!(api_def.apis.len(), 2);

        let cursor = api_def
            .apis
            .iter()
            .find(|a| a.name == "Cursor")
            .expect("Cursor api");
        assert_eq!(cursor.doc_comments, vec!["Cursor control."]);
        assert_eq!(cursor.functions.len(), 4);

        let set = &cursor.functions[0];
        assert_eq!(set.name, "set");
        assert_eq!(set.c_name, "fl_cursor_set", "body spelled fl_<domain>_<fn>");
        assert_eq!(set.doc_comments, vec!["Request a shape."]);
        assert_eq!(set.function_args.len(), 1);
        assert_eq!(set.function_args[0].name, "cursor");
        assert_eq!(set.function_args[0].type_name, "Cursor");
        assert!(!set.has_varargs);

        let get = &cursor.functions[1];
        assert!(
            get.function_args.is_empty(),
            "a no-arg api fn has zero args, not a self"
        );
        assert_eq!(get.return_val.as_ref().expect("ret").type_name, "Cursor");

        let format = api_def
            .apis
            .iter()
            .find(|a| a.name == "Format")
            .expect("Format api");
        let fs = &format.functions[0];
        assert_eq!(fs.c_name, "fl_format_frame_string");
        assert!(fs.has_varargs, "the trailing ... sets has_varargs");
        assert_eq!(
            fs.function_args.len(),
            1,
            "varargs is dropped from explicit args"
        );
        assert_eq!(fs.function_args[0].type_name, "char");
        assert!(fs.function_args[0].const_pointer);
        assert_eq!(
            fs.return_val.as_ref().expect("ret").vtype,
            VariableType::Str
        );
    }

    #[test]
    fn the_zero_variant_follows_c_sequential_numbering() {
        let zero_of = |src: &str| {
            let mut api_def = ApiDef::default();
            ApiParser::parse_string(src, "t.def", &mut api_def);
            zero_variant(&api_def.enums[0]).map(str::to_owned)
        };

        assert_eq!(zero_of("enum A {\n Any,\n One,\n}").as_deref(), Some("Any"));
        assert_eq!(
            zero_of("enum A {\n Loud = 1,\n Quiet = 0,\n}").as_deref(),
            Some("Quiet")
        );
        // B is 2 by sequence, not 0 by position.
        assert_eq!(zero_of("enum A {\n A = 1,\n B,\n}"), None);
        assert_eq!(zero_of("enum A {\n A = 1,\n B = 2,\n}"), None);
        assert_eq!(
            zero_of("enum A {\n A = 0x0,\n B = 0x10000,\n}").as_deref(),
            Some("A")
        );
    }

    #[test]
    fn an_extern_opaque_view_reaches_the_args_naming_it() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[view(flowi::Arena)]\n\
             extern opaque FlArena\n\
             extern opaque UiCtx\n\
             api Demozoo { get(id: u32, arena: *FlArena, ui: *UiCtx) -> u32 }",
            "demozoo.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        assert_eq!(api_def.externs[0].view.as_deref(), Some("flowi::Arena"));
        assert_eq!(api_def.externs[1].view, None);

        let args = &api_def.apis[0].functions[0].function_args;
        assert_eq!(args[1].opaque_view.as_deref(), Some("flowi::Arena"));
        assert_eq!(args[2].opaque_view, None);
    }

    #[test]
    fn extern_opaque_parses_and_resolves_on_fn_fields() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "extern opaque UiCtx\n\
             extern opaque FlArena\n\
             enum Device { Keyboard, Mouse }\n\
             struct Backend {\n\
                 ctx: *void,\n\
                 home: *UiCtx,\n\
                 poll(ctx: *void, ui: *UiCtx) -> bool,\n\
                 clip(ctx: *void, arena: *FlArena) -> Device,\n\
             }",
            "backend.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        assert_eq!(api_def.externs.len(), 2);
        assert_eq!(api_def.externs[0].name, "UiCtx");
        assert_eq!(api_def.externs[0].kind, ExternKind::Opaque);
        assert_eq!(api_def.externs[1].name, "FlArena");

        let backend = api_def
            .structs
            .iter()
            .find(|s| s.name == "Backend")
            .expect("struct");
        assert_eq!(backend.variables.len(), 2, "ctx + home are value fields");
        assert_eq!(
            backend.functions.len(),
            2,
            "poll + clip are function-fields"
        );

        let home = backend
            .variables
            .iter()
            .find(|v| v.name == "home")
            .expect("home field");
        assert!(home.is_extern_opaque, "*UiCtx value field is extern-opaque");
        let ctx_field = backend
            .variables
            .iter()
            .find(|v| v.name == "ctx")
            .expect("ctx field");
        assert!(
            !ctx_field.is_extern_opaque,
            "void* value field is not extern-opaque"
        );

        let poll = &backend.functions[0];
        let ui_arg = poll
            .function_args
            .iter()
            .find(|a| a.name == "ui")
            .expect("ui arg");
        assert!(ui_arg.is_extern_opaque, "*UiCtx arg is extern-opaque");
        let ctx_arg = poll
            .function_args
            .iter()
            .find(|a| a.name == "ctx")
            .expect("ctx arg");
        assert!(!ctx_arg.is_extern_opaque, "void* ctx is not extern-opaque");
        let clip = &backend.functions[1];
        assert!(
            clip.function_args
                .iter()
                .find(|a| a.name == "arena")
                .unwrap()
                .is_extern_opaque
        );
        let ret = clip.return_val.as_ref().expect("ret");
        assert!(
            !ret.is_extern_opaque,
            "a generated enum return is not extern-opaque"
        );
        assert_eq!(ret.vtype, VariableType::Regular);
    }

    #[test]
    fn mod_directives_collect_into_mods() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(render)]\n\
             mod render_ir\n\
             mod image\n\
             struct Backend { frame: *RenderFrame }",
            "backend.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        assert_eq!(api_def.module, "render", "#[module] sets the output module");
        assert_eq!(
            api_def.mods,
            vec!["render_ir", "image"],
            "mods in declaration order"
        );

        // The referenced-but-unauthored payload stays an ordinary named type; the
        // mod include supplies the definition.
        let frame = &api_def.structs[0].variables[0];
        assert_eq!(frame.type_name, "RenderFrame");
        assert_eq!(frame.vtype, VariableType::Regular);
        assert!(
            !frame.is_extern_opaque,
            "a mod-provided type is not extern-opaque"
        );
    }

    #[test]
    fn callback_parses_with_named_args_and_resolves() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "extern opaque FlVfsEntry\n\
             /// List one entry.\n\
             callback VfsListingCallback(user_data: *void, entry: *const FlVfsEntry) -> bool",
            "vfs_listing.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        assert!(api_def.has_callbacks(), "a callback-only def has callbacks");
        assert_eq!(api_def.callbacks.len(), 1);
        let cb = &api_def.callbacks[0];
        assert_eq!(cb.name, "VfsListingCallback");
        assert_eq!(cb.doc_comments, vec!["List one entry."]);
        assert_eq!(cb.function_args.len(), 2);
        assert!(
            cb.function_args
                .iter()
                .all(|a| a.vtype != VariableType::SelfType),
            "no self receiver"
        );

        let user_data = &cb.function_args[0];
        assert_eq!(user_data.name, "user_data");
        assert_eq!(user_data.type_name, "void");
        assert!(user_data.pointer && !user_data.const_pointer, "*void");

        let entry = &cb.function_args[1];
        assert_eq!(entry.name, "entry");
        assert_eq!(entry.type_name, "FlVfsEntry");
        assert!(entry.const_pointer, "*const FlVfsEntry");
        assert!(
            entry.is_extern_opaque,
            "the extern-opaque arg is flagged by the cross-file pass"
        );

        let ret = cb.return_val.as_ref().expect("bool return");
        assert_eq!(ret.vtype, VariableType::Primitive);
        assert_eq!(ret.type_name, "bool");
    }

    #[test]
    fn manual_marker_on_api_fn_parses() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api TextInput {\n\
                 [manual] create(capacity: u32) -> u32\n\
                 set(font: u32)\n\
             }",
            "text_input.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let api = api_def
            .apis
            .iter()
            .find(|a| a.name == "TextInput")
            .expect("api");
        let create = api
            .functions
            .iter()
            .find(|f| f.name == "create")
            .expect("create");
        assert_eq!(
            create.func_type,
            FunctionType::Manual,
            "[manual] marks it Manual"
        );
        assert_eq!(create.c_name, "fl_text_input_create");
        let set = api.functions.iter().find(|f| f.name == "set").expect("set");
        assert_eq!(
            set.func_type,
            FunctionType::Static,
            "unmarked api fn stays Static"
        );
    }

    #[test]
    fn raii_markers_on_api_fn_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api SelectionSet {\n\
                 [drop] destroy(set: *void)\n\
                 [const] contains(set: *void, id: u64) -> bool\n\
                 [rename(clear)] clear_all(set: *void)\n\
                 set(set: *void, id: u64, selected: bool)\n\
             }",
            "ui_selection.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let api = api_def
            .apis
            .iter()
            .find(|a| a.name == "SelectionSet")
            .expect("api");

        let destroy = api
            .functions
            .iter()
            .find(|f| f.name == "destroy")
            .expect("destroy");
        assert!(destroy.is_drop, "[drop] flags the destructor");
        assert_eq!(
            destroy.c_name, "fl_selection_set_destroy",
            "c_name unaffected by [drop]"
        );

        let contains = api
            .functions
            .iter()
            .find(|f| f.name == "contains")
            .expect("contains");
        assert!(contains.is_const, "[const] flags the &self slot");
        assert!(!contains.is_drop && contains.rename.is_none());

        let clear = api
            .functions
            .iter()
            .find(|f| f.name == "clear_all")
            .expect("clear_all");
        assert_eq!(
            clear.rename.as_deref(),
            Some("clear"),
            "[rename(clear)] overrides the method name"
        );
        assert_eq!(
            clear.c_name, "fl_selection_set_clear_all",
            "c_name keeps the original slot name"
        );

        let set = api.functions.iter().find(|f| f.name == "set").expect("set");
        assert!(
            !set.is_drop && !set.is_const && set.rename.is_none(),
            "an unmarked slot carries no RAII markers"
        );
    }

    /// Parse one def source through the cross-file pass.
    fn resolved(src: &str, file: &str) -> ApiDef {
        let mut def = ApiDef::default();
        ApiParser::parse_string(src, file, &mut def);
        ApiParser::second_pass(std::slice::from_mut(&mut def), &crate::naming::FL);
        def
    }

    #[test]
    fn mirror_attribute_annotates_referring_slot_args() {
        let def = resolved(
            "#[attributes(Mirror)]\n\
             struct WidgetConfig { id_override: String, tab_index: i32, }\n\
             struct PlainConfig { z: i16, }\n\
             api Button {\n\
                 new_impl(config: WidgetConfig, other: PlainConfig) -> bool\n\
             }",
            "widget_config.def",
        );

        let args = &def.apis[0].functions[0].function_args;
        assert_eq!(
            args[0].mirror,
            Some(MirrorRef {
                module: "widget_config".to_owned(),
                lifetime: true,
            }),
            "a mirrored config arg records its twin's module, and the string field gives it a borrow"
        );
        assert_eq!(
            args[1].mirror, None,
            "an unmirrored config arg is untouched"
        );
    }

    #[test]
    fn mirror_without_borrowed_fields_carries_no_lifetime() {
        let def = resolved(
            "#[attributes(Mirror)]\n\
             struct PlainConfig { z: i16, }\n\
             api Popup { open(config: PlainConfig) }",
            "plain_config.def",
        );
        let mirror = def.apis[0].functions[0].function_args[0]
            .mirror
            .as_ref()
            .expect("mirrored");
        assert!(!mirror.lifetime, "no string or pointer field, no borrow");
    }

    #[test]
    #[should_panic(expected = "no 0-valued variant")]
    fn mirror_rejects_enum_field_without_a_zero_variant() {
        resolved(
            "enum Align { Left = 1, Right = 2, }\n\
             #[attributes(Mirror)]\n\
             struct BadConfig { align: Align, }",
            "bad_config.def",
        );
    }

    #[test]
    fn mirror_field_records_the_nested_twin() {
        let def = resolved(
            "#[attributes(Mirror)]\n\
             struct WidgetConfig { id_override: String, }\n\
             #[attributes(Mirror)]\n\
             struct CheckboxConfig { label_on_left: bool, widget: WidgetConfig, }",
            "widget_config.def",
        );
        let checkbox = def
            .structs
            .iter()
            .find(|s| s.name == "CheckboxConfig")
            .expect("parsed");
        assert_eq!(
            checkbox.variables[1].mirror,
            Some(MirrorRef {
                module: "widget_config".to_owned(),
                lifetime: true,
            }),
            "the nested field records the twin's module, and the twin borrows"
        );
        assert_eq!(
            checkbox.variables[0].mirror, None,
            "a plain by-value field is untouched"
        );
    }

    #[test]
    fn mirror_lifetime_propagates_through_a_nested_twin() {
        let def = resolved(
            "#[attributes(Mirror)]\n\
             struct WidgetConfig { id_override: String, }\n\
             #[attributes(Mirror)]\n\
             struct ProgressConfig { widget: WidgetConfig, }\n\
             #[attributes(Mirror)]\n\
             struct GaugeConfig { progress: ProgressConfig, }\n\
             api Gauge {\n\
             show(config: GaugeConfig)\n\
             }",
            "widget_config.def",
        );
        let arg = &def.apis[0].functions[0].function_args[0];
        assert!(
            arg.mirror.as_ref().expect("mirrored").lifetime,
            "the borrow reaches GaugeConfig two levels up from the string"
        );
    }

    #[test]
    #[should_panic(expected = "contains itself by value")]
    fn mirror_rejects_a_containment_cycle() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct AConfig { b: BConfig, }\n\
             #[attributes(Mirror)]\n\
             struct BConfig { a: AConfig, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "mutable pointer")]
    fn mirror_rejects_a_mutable_pointer_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { state: *TextInputState, }",
            "bad_config.def",
        );
    }

    #[test]
    fn mirror_admits_a_mutable_pointer_to_an_opaque_type() {
        let def = resolved(
            "#[attributes(Opaque)]\n\
             struct TextInputState {}\n\
             #[attributes(Mirror)]\n\
             struct DropdownConfig { search_state: *TextInputState, }",
            "widget_config.def",
        );
        let dropdown = def
            .structs
            .iter()
            .find(|s| s.name == "DropdownConfig")
            .expect("parsed");
        assert!(
            dropdown.variables[0].pointer,
            "the handle field keeps its raw pointer crossing"
        );
    }

    #[test]
    #[should_panic(expected = "C string")]
    fn mirror_rejects_a_c_string_pointer_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { format: *const char, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "is a function field")]
    fn mirror_rejects_a_function_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { on_click(ud: *void) -> bool, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "is a union")]
    fn mirror_rejects_a_union_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { payload: union { a: f32, b: i32 }, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "is an array")]
    fn mirror_rejects_an_array_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { corners: [f32; 4], }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "is a string pointer")]
    fn mirror_rejects_a_string_pointer_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { label: *const String, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "untyped or opaque pointer")]
    fn mirror_rejects_a_void_pointer_field() {
        resolved(
            "#[attributes(Mirror)]\n\
             struct BadConfig { user_data: *const void, }",
            "bad_config.def",
        );
    }

    #[test]
    #[should_panic(expected = "untyped or opaque pointer")]
    fn mirror_rejects_an_extern_opaque_pointer_field() {
        resolved(
            "extern opaque FlArena\n\
             #[attributes(Mirror)]\n\
             struct BadConfig { arena: *const FlArena, }",
            "bad_config.def",
        );
    }

    #[test]
    fn array_param_marker_parses() {
        let def = resolved(
            "api Hash { lookup([array(u8, 16)] md5: *const u8, subsong: u16) -> u32 }",
            "hash.def",
        );
        let arg = &def.apis[0].functions[0].function_args[0];
        assert_eq!(arg.array_param, Some(("u8".to_owned(), "16".to_owned())));
        assert!(arg.const_pointer && arg.type_name == "u8" && arg.array.is_none());
    }

    /// The marker only adds the length the pointer type cannot carry.
    #[test]
    #[should_panic(expected = "must be spelled `md5: *const u8`")]
    fn array_param_rejects_a_mismatched_pointer() {
        resolved(
            "api Hash { lookup([array(u8, 16)] md5: *const u16) -> u32 }",
            "hash.def",
        );
    }

    #[test]
    #[should_panic(expected = "positive integer literal")]
    fn array_param_rejects_a_named_length() {
        resolved(
            "api Hash { lookup([array(u8, MD5_LEN)] md5: *const u8) -> u32 }",
            "hash.def",
        );
    }

    #[test]
    #[should_panic(expected = "ABI-broken")]
    fn bare_sized_array_param_is_rejected() {
        resolved("api Hash { lookup(md5: [u8; 16]) -> u32 }", "hash.def");
    }

    #[test]
    #[should_panic(expected = "ABI-broken")]
    fn bare_sized_array_callback_param_is_rejected() {
        resolved("callback HashSink(md5: [u8; 16])", "hash.def");
    }

    #[test]
    fn pairing_annotations_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(demozoo)]\n\
             #[views(crate::demoscene::data)]\n\
             #[view(crate::demoscene::query::SortOrder, fallback = TitleAz)]\n\
             enum Sort { NameAsc, [from(TitleZa)] NameDesc, }\n\
             #[view(crate::demoscene::catalog::QueryView)]\n\
             #[read(Held)]\n\
             struct Query {\n\
                 [from(entities)] entity_mask: u32,\n\
                 [from(tree)] [with(crate::demozoo_abi::read_tree)] expr: *const u32,\n\
                 expr_count: u32,\n\
                 [fixed(Ready)] status: Status,\n\
             }",
            "demozoo.def",
            &mut api_def,
        );

        assert_eq!(api_def.views.as_deref(), Some("crate::demoscene::data"));

        let sort = &api_def.enums[0];
        let view = sort.view.as_ref().expect("enum view");
        assert_eq!(view.path, "crate::demoscene::query::SortOrder");
        assert_eq!(view.fallback.as_deref(), Some("TitleAz"));
        assert_eq!(sort.entries[0].from_host, None);
        assert_eq!(sort.entries[1].from_host.as_deref(), Some("TitleZa"));

        let query = &api_def.structs[0];
        let view = query.view.as_ref().expect("struct view");
        assert_eq!(view.path, "crate::demoscene::catalog::QueryView");
        assert_eq!(view.fallback, None);
        assert_eq!(query.variables[0].from_host.as_deref(), Some("entities"));
        assert_eq!(query.variables[1].from_host.as_deref(), Some("tree"));
        assert_eq!(
            query.variables[1].with_helper.as_deref(),
            Some("crate::demozoo_abi::read_tree")
        );
        assert_eq!(query.variables[2].name, "expr_count");
        assert_eq!(query.variables[3].fixed.as_deref(), Some("Ready"));
        assert!(query.read);
        assert_eq!(query.read_owned.as_deref(), Some("Held"));
    }

    /// A path is `name(::name)*` and nothing else.
    #[test]
    #[should_panic(expected = "ApiParser: demozoo.def")]
    fn a_trailing_path_separator_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string("#[views(crate::)]", "demozoo.def", &mut api_def);
    }

    #[test]
    #[should_panic(expected = "ApiParser: demozoo.def")]
    fn a_digit_leading_path_segment_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string("#[views(crate::2data)]", "demozoo.def", &mut api_def);
    }

    #[test]
    #[should_panic(expected = "ApiParser: demozoo.def")]
    fn a_quoted_view_path_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[view(\"crate::data\")]\nstruct Query { id: u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    /// The field attributes live on the struct-field rule only: an api parameter
    /// shares the var rule and stays untouched.
    #[test]
    #[should_panic(expected = "ApiParser: demozoo.def")]
    fn a_field_attribute_on_a_parameter_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api Demozoo { get([from(id)] work_id: u32) -> u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    fn doc_comments_survive_pairing_annotations() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "/// Which orderings exist.\n\
             enum Sort {\n\
                 /// A to Z.\n\
                 [from(TitleAz)] NameAsc,\n\
                 /// Z to A.\n\
                 NameDesc,\n\
             }\n\
             struct Query {\n\
                 /// What to match.\n\
                 text: String,\n\
                 /// Which kinds.\n\
                 [from(entities)] entity_mask: u32,\n\
             }",
            "demozoo.def",
            &mut api_def,
        );

        let sort = &api_def.enums[0];
        assert_eq!(sort.entries[0].doc_comments, ["A to Z."]);
        assert_eq!(sort.entries[0].from_host.as_deref(), Some("TitleAz"));
        assert_eq!(sort.entries[1].doc_comments, ["Z to A."]);

        let query = &api_def.structs[0];
        assert_eq!(query.variables[0].doc_comments, ["What to match."]);
        assert_eq!(query.variables[1].doc_comments, ["Which kinds."]);
        assert_eq!(query.variables[1].from_host.as_deref(), Some("entities"));
    }

    #[test]
    #[should_panic(expected = "pairing annotations apply to value fields only")]
    fn a_pairing_annotation_on_a_union_field_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Event { [from(payload)] body: union { x: u32, y: u32 } }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "pairing annotations apply to value fields only")]
    fn a_pairing_annotation_on_a_function_field_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Ops { [from(reader)] read(size: u32) -> u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "is a struct-field annotation, not an enum one")]
    fn a_fixed_annotation_on_an_enum_variant_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "enum Sort { [fixed(Ready)] NameAsc, }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "pairing annotations apply to value fields only")]
    fn a_fixed_annotation_on_a_union_field_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Event { [fixed(Ready)] body: union { x: u32, y: u32 } }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "is a struct-field annotation, not an enum one")]
    fn a_with_annotation_on_an_enum_variant_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "enum Sort { [with(crate::read_sort)] NameAsc, }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "`fallback` is an enum arm")]
    fn a_fallback_on_a_struct_view_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[view(crate::data::QueryView, fallback = Empty)]\nstruct Query { id: u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "one `[from(b)]` per field")]
    fn a_repeated_field_annotation_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Query { [from(a)] [from(b)] id: u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    #[should_panic(expected = "one `[read_with(b::c)]` per field")]
    fn a_repeated_read_with_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Query { [read_with(a::b)] [read_with(b::c)] id: u32 }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    fn field_annotations_combine_in_any_order() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Query {\n\
                 [from(a)] [read_with(x::y)] id: u32,\n\
                 [read_with(p::q)] [from(b)] [with(m::n)] tag: u32,\n\
             }",
            "demozoo.def",
            &mut api_def,
        );

        let fields = &api_def.structs[0].variables;
        assert_eq!(fields[0].from_host.as_deref(), Some("a"));
        assert_eq!(fields[0].read_with.as_deref(), Some("x::y"));
        assert_eq!(fields[1].from_host.as_deref(), Some("b"));
        assert_eq!(fields[1].with_helper.as_deref(), Some("m::n"));
        assert_eq!(fields[1].read_with.as_deref(), Some("p::q"));
    }

    #[test]
    #[should_panic(expected = "`[read_with(a::b)]` is a struct-field annotation")]
    fn a_read_with_on_an_enum_variant_is_rejected() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "enum Sort { [read_with(a::b)] NameAsc }",
            "demozoo.def",
            &mut api_def,
        );
    }

    #[test]
    fn reads_directive_and_read_marker_parse() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[reads(crate::services::demozoo)]\n\
             struct Party { id: u32 }\n\
             #[read]\n\
             struct PartyDetail { id: u32 }",
            "demozoo.def",
            &mut api_def,
        );

        assert_eq!(api_def.reads.as_deref(), Some("crate::services::demozoo"));
        assert!(!api_def.structs[0].read);
        assert!(api_def.structs[1].read);
    }

    #[test]
    fn every_banned_token_is_caught_in_a_plain_comment() {
        let cases = [
            ("// Pointer-only dep (ADR-0035).", "ADR reference"),
            ("extern opaque FlArena // see #123", "issue reference"),
            (
                "// The driver side (vfs_plugin.def).",
                "source-file pointer",
            ),
            (
                "// The hand-written leaf (vfs_api.h).",
                "source-file pointer",
            ),
            (
                "// Exposed to Rust through the generated direct API.",
                "generator-meta phrase",
            ),
            (
                "/// Still caught behind three slashes (ADR-0044).",
                "ADR reference",
            ),
        ];

        for (source, expected) in cases {
            let violations = ApiParser::comment_policy_violations(source);
            assert!(
                violations.iter().any(|v| v.contains(expected)),
                "{source:?} should report {expected:?}, got {violations:?}"
            );
        }
    }

    #[test]
    fn a_clean_plain_comment_parses() {
        assert!(ApiParser::comment_policy_violations("// The scratch arena.").is_empty());

        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "// The scratch arena.\n\
             extern opaque FlArena",
            "demozoo.def",
            &mut api_def,
        );

        assert_eq!(api_def.externs[0].name, "FlArena");
    }

    #[test]
    #[should_panic(expected = "comment policy violation(s) in demozoo.def")]
    fn a_banned_token_in_a_plain_comment_fails_generation() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "// Pointer-only dep (ADR-0035).\n\
             extern opaque FlArena",
            "demozoo.def",
            &mut api_def,
        );
    }
}
