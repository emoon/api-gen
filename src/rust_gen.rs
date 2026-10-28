// Rust generation.
//
// Each data type emits a `#[repr(C)]` struct/enum spelled by the unprefixed IDL
// name plus a const _ layout assertion built from the IDL-computed
// offsets/size (layout.rs). An `api <Domain>` block additionally emits an
// extern "C" block declaring the domain's direct `fl_*` functions, which the
// ergonomic façade forwards to. No rustfmt post-pass - output is
// hand-canonicalised so regeneration is a no-op diff.

use crate::api_parser::*;
use crate::layout::TypeRegistry;
use crate::naming::Naming;
use crate::pairing::PairedModel;
use crate::read_gen;
use heck::{ToShoutySnakeCase, ToSnakeCase};
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

pub struct RustGen;

/// The two safe Rust surfaces over the same loose C symbols. The semantic
/// classification is shared; this selects only crate-local spelling/policy
/// (for example, which string helper owns the bytes for the call).
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LooseSymbolSurface {
    DirectLink,
    ExternalConsumer,
}

#[derive(Debug, Eq, PartialEq)]
struct LoweredArgs {
    params: Vec<String>,
    ffi: Vec<String>,
    prelude: Vec<String>,
}

#[derive(Debug, Eq, PartialEq)]
enum LoweredResult {
    Unit,
    Value { ty: String, wrap: Option<String> },
    Status { ok_ty: String, has_out: bool },
    Option { ty: String },
    Transfer { owned_ty: String },
}

/// What a service wrapper needs to answer an owned record instead of the raw one:
/// the paired model saying which records read back, and where the generated
/// readers live (`<path>::<def>_read`).
pub struct ServiceReads<'a> {
    pub model: &'a PairedModel,
    pub path: &'a str,
}

/// The record a slot answers through a generated reader, when it answers one.
struct ReadRecord {
    /// Consume-side type the reader builds, 'a-parameterised.
    owned: String,
    /// Path of the generated reader function.
    reader: String,
    /// The record carries found, so the reader answers an Option.
    optional: bool,
}

/// Clippy's too_many_arguments threshold. A generated forwarder past it gets a
/// per-method allow - its arity comes from the C prototype it mirrors.
const CLIPPY_MAX_ARGS: usize = 7;

/// Module-level safety documentation for a generated file that contains unsafe
/// blocks. The allow is what makes the shared statement satisfy
/// undocumented_unsafe_blocks; a block that needs a different argument gets its
/// own // SAFETY: comment from the generator.
static RUST_GENERATED_SAFETY_HEADER: &str = "\
//! SAFETY: the unsafe blocks below are generated forwarders. Each wraps one call
//! to an exported C symbol of the linked library, over arguments this generator
//! lowered from safe Rust values, and imposes no further invariant on the caller.
//! Blocks that carry an argument beyond this one document it at the site.
#![allow(clippy::undocumented_unsafe_blocks)]
";

/// Per-site safety note for reading a slot's out-param back with assume_init, at
/// indent - the one block whose obligation the module header above does not cover,
/// since it rests on the slot's own contract rather than on arguments this generator
/// lowered. reported names how the shape reports success (a status code, or a
/// bool return).
fn safety_assume_init(indent: &str, reported: &str) -> String {
    format!(
        "{indent}// SAFETY: the slot reported {reported}, and it writes its out-param\n\
         {indent}// before reporting it.\n"
    )
}

impl RustGen {
    /// Crate path a surface reaches the generated ABI types through: the direct-link
    /// façade names them flowi_sys::; an external consumer carries its own copy of
    /// the defs and may not depend on flowi_sys at all, so it names them crate::.
    fn loose_symbol_crate_root(surface: LooseSymbolSurface) -> &'static str {
        match surface {
            LooseSymbolSurface::DirectLink => "flowi_sys",
            LooseSymbolSurface::ExternalConsumer => "crate",
        }
    }

    fn loose_symbol_base_type(surface: LooseSymbolSurface, var: &Variable) -> String {
        // An extern opaque dep is declared module-locally, so it is referenced
        // unqualified on either surface.
        if var.is_extern_opaque {
            return var.type_name.clone();
        }
        let root = Self::loose_symbol_crate_root(surface);
        if var.vtype == VariableType::Str {
            return format!("{}::RawStr", root);
        }
        match var.vtype {
            VariableType::Primitive => Self::ffi_primitive(&var.type_name),
            _ => format!("{}::{}", root, var.type_name),
        }
    }

    /// Copy the &str expr evaluates to into the per-frame arena, inline, through the
    /// exported C primitive fl_frame_str. expr is evaluated once.
    ///
    /// The emitted expression calls an unsafe extern "C" function, so every caller
    /// must place it inside an unsafe block.
    fn arena_str_expr(expr: &str) -> String {
        format!(
            "{{ let s = {}; flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()) }}",
            expr
        )
    }

    /// Turn the &str expr evaluates to into the RawStr the ABI takes. The façade
    /// copies into the per-frame arena (inline fl_frame_str) unless the slot is
    /// `[borrowed]` (the callee copies before returning, so the caller's bytes can be
    /// pointed at directly); an external consumer has no frame arena and always borrows.
    fn lower_string_arg(surface: LooseSymbolSurface, func: &Function, expr: &str) -> String {
        match surface {
            LooseSymbolSurface::DirectLink if !func.is_borrowed => Self::arena_str_expr(expr),
            LooseSymbolSurface::DirectLink => format!("flowi_sys::RawStr::borrow({})", expr),
            LooseSymbolSurface::ExternalConsumer => format!("crate::RawStr::borrow({})", expr),
        }
    }

    fn lower_loose_symbol_arg(
        surface: LooseSymbolSurface,
        func: &Function,
        arg: &Variable,
    ) -> Result<(Option<String>, String, Vec<String>), String> {
        let name = Self::rust_ident(&arg.name);
        if surface == LooseSymbolSurface::DirectLink
            && arg.type_name == "LayoutId"
            && arg.vtype == VariableType::Regular
        {
            return Ok((
                Some(format!("{}: impl Into<crate::LayoutId>", name)),
                format!("{}.into().into_sys()", name),
                Vec::new(),
            ));
        }
        if arg.is_extern_opaque {
            // `#[view(<path>)]` on the dep names the safe reference standing in for the
            // pointer. The borrow is 'a because the only slot accepting one answers a
            // record read back out of it.
            if surface == LooseSymbolSurface::ExternalConsumer {
                if let Some(view) = &arg.opaque_view {
                    return Ok((
                        Some(format!("{}: &'a {}", name, view)),
                        format!("{}.as_raw().cast()", name),
                        Vec::new(),
                    ));
                }
            }
            return Err(format!(
                "slot `{}`: unclassifiable `extern opaque` pointer parameter `{}` (`{}`); \
                 no safe reference to an opaque host type exists — mark the slot `[manual]`",
                func.name, arg.name, arg.type_name
            ));
        }
        if arg.is_transfer {
            if arg.type_name == "void" || !(arg.pointer || arg.const_pointer) {
                return Err(format!(
                    "slot `{}`: a `[transfer]` parameter must be a pointer to a named type (got `{}`)",
                    func.name, arg.type_name
                ));
            }
            let owned_ty = Self::owned_newtype_name(&arg.type_name);
            return Ok((
                Some(format!("{}: {}", name, owned_ty)),
                format!("{}_ptr", name),
                vec![format!("let {}_ptr = {}.into_raw();", name, name)],
            ));
        }
        if arg.vtype == VariableType::Str {
            return Ok((
                Some(format!("{}: impl AsRef<str>", name)),
                Self::lower_string_arg(surface, func, &format!("{}.as_ref()", name)),
                Vec::new(),
            ));
        }
        // A `#[attributes(Mirror)]` config crosses the façade as its safe twin, which
        // to_sys packs - copying each string into the per-frame arena - at the call.
        // The arena is a façade-only resource, so an external consumer keeps the raw
        // ABI struct.
        if surface == LooseSymbolSurface::DirectLink && !arg.pointer && !arg.const_pointer {
            if let Some(mirror) = &arg.mirror {
                return Ok((
                    Some(format!(
                        "{}: {}",
                        name,
                        Self::mirror_ref_path(&arg.type_name, mirror)
                    )),
                    format!("{}.to_sys()", name),
                    Vec::new(),
                ));
            }
        }
        if arg.type_name == "void" && (arg.pointer || arg.const_pointer) {
            return Err(format!(
                "slot `{}`: unclassifiable `void` pointer parameter `{}`; mark the slot \
                 `[manual]` or give it a typed pointer",
                func.name, arg.name
            ));
        }
        // A `*const <primitive>` parameter is a counted buffer with the count kept
        // outside the type. Lowering it to &u8 would promise the callee one element
        // while its contract reads sixteen, so safe caller code could drive an
        // out-of-bounds read.
        //
        // Deliberately const only: a `*mut <primitive>` is the write-back-one-value
        // shape (`fl_checkbox(label, bool* checked)` -> &mut bool), and a mutable
        // counted buffer is not distinguishable from it by type alone, so it is marked
        // `[slice_mut(T)]` at the def rather than guessed at here.
        if arg.const_pointer && arg.vtype == VariableType::Primitive {
            return Err(format!(
                "slot `{}`: `*const {}` parameter `{}` is a counted buffer whose length \
                 lives outside the type; a `&{}` would promise the callee one element. \
                 Mark the data arg `[slice({})]` so it crosses as a slice plus the \
                 following count arg, or mark the slot `[manual]`",
                func.name,
                arg.type_name,
                arg.name,
                Self::ffi_primitive(&arg.type_name),
                arg.type_name
            ));
        }
        let base = Self::loose_symbol_base_type(surface, arg);
        if arg.const_pointer {
            if func.is_retained && surface == LooseSymbolSurface::DirectLink {
                let slot = format!("RETAINED_{}", arg.name.to_uppercase());
                let prelude = vec![
                    format!(
                        "static mut {}: core::mem::MaybeUninit<{}> = core::mem::MaybeUninit::uninit();",
                        slot, base
                    ),
                    format!(
                        "let {}_owned = core::ptr::addr_of_mut!({}).cast::<{}>();",
                        name, slot, base
                    ),
                    format!(
                        "core::ptr::copy_nonoverlapping({} as *const {}, {}_owned, 1);",
                        name, base, name
                    ),
                ];
                return Ok((
                    Some(format!("{}: &{}", name, base)),
                    format!("{}_owned as *const {}", name, base),
                    prelude,
                ));
            }
            let lifetime = if func.is_retained { "&'static " } else { "&" };
            return Ok((
                Some(format!("{}: {}{}", name, lifetime, base)),
                format!("{} as *const {}", name, base),
                Vec::new(),
            ));
        }
        if arg.pointer {
            return Ok((
                Some(format!("{}: &mut {}", name, base)),
                format!("{} as *mut {}", name, base),
                Vec::new(),
            ));
        }
        Ok((Some(format!("{}: {}", name, base)), name, Vec::new()))
    }

    fn lower_loose_symbol_args(
        surface: LooseSymbolSurface,
        func: &Function,
        handle: Option<&str>,
        out_idx: Option<usize>,
    ) -> Result<LoweredArgs, String> {
        let mut lowered = LoweredArgs {
            params: Vec::new(),
            ffi: Vec::new(),
            prelude: Vec::new(),
        };
        let mut i = 0;
        while i < func.function_args.len() {
            let arg = &func.function_args[i];
            if Some(i) == out_idx {
                lowered.ffi.push("out.as_mut_ptr()".to_owned());
                i += 1;
                continue;
            }
            if handle == Some(arg.name.as_str()) {
                lowered.ffi.push("self.handle".to_owned());
                i += 1;
                continue;
            }
            if let Some(elem) = arg.slice_elem.as_deref() {
                let name = Self::rust_ident(&arg.name);
                let elem_ty = Self::facade_slice_elem_type(surface, elem);
                let base = Self::loose_symbol_base_type(surface, arg);
                let ptr_kind = if arg.const_pointer { "*const" } else { "*mut" };
                let as_ptr = if arg.slice_mut {
                    "as_mut_ptr"
                } else {
                    "as_ptr"
                };
                // The cast reinterprets the slice's element type as the one the ABI
                // declares - `[slice(u64)] ids: *void` crosses as `*const c_void`. When
                // the two already agree the cast is a no-op that clippy's
                // unnecessary_cast flags, so it is emitted only where it converts.
                let ptr_expr = if elem_ty == base {
                    format!("{}.{}()", name, as_ptr)
                } else {
                    format!("{}.{}() as {} {}", name, as_ptr, ptr_kind, base)
                };
                if arg.slice_mut {
                    lowered.params.push(format!("{}: &mut [{}]", name, elem_ty));
                } else {
                    lowered.params.push(format!("{}: &[{}]", name, elem_ty));
                }
                lowered.ffi.push(ptr_expr);
                let count = func
                    .function_args
                    .get(i + 1)
                    .expect("a [slice] arg must be followed by its count arg");
                lowered
                    .ffi
                    .push(format!("{}.len() as {}", name, count.type_name));
                i += 2;
                continue;
            }
            // `[array(T, N)]`: the parser pinned the arg to `*const T`, so the
            // reference's as_ptr() is exactly the declared crossing.
            if let Some((elem, len)) = arg.array_param.as_ref() {
                let name = Self::rust_ident(&arg.name);
                let elem_ty = Self::facade_slice_elem_type(surface, elem);
                lowered
                    .params
                    .push(format!("{}: &[{}; {}]", name, elem_ty, len));
                lowered.ffi.push(format!("{}.as_ptr()", name));
                i += 1;
                continue;
            }
            if matches!(arg.array, Some(ArrayType::Unsized)) {
                let name = Self::rust_ident(&arg.name);
                if arg.vtype == VariableType::Str {
                    // A `[*const String]` arg is the array form of the scalar String
                    // lowering: the safe param is `&[impl AsRef<str>]` and the
                    // string-mirror array the ABI takes is packed at the call site. The
                    // mirror is a raw pointer + packed-length pair with no safe
                    // constructor, so it never reaches the signature.
                    //
                    // Both halves come from the frame arena and nothing else -
                    // fl_frame_str_array reserves the slots, fl_frame_str copies each
                    // string into them. No heap allocation, no fixed cap on the element
                    // count; the whole list dies with the frame.
                    if arg.pointer {
                        return Err(format!(
                            "slot `{}`: mutable string array `{}` has no safe façade lowering \
                             (a string-mirror out-array is unreadable from safe code); mark the \
                             slot `[manual]`",
                            func.name, arg.name
                        ));
                    }
                    // The frame arena is a façade-only resource: an external consumer has no live
                    // frame to allocate from, and a `[borrowed]` slot's whole point is not copying.
                    if surface != LooseSymbolSurface::DirectLink || func.is_borrowed {
                        return Err(format!(
                            "slot `{}`: string array `{}` needs the frame arena, which only the \
                             ordinary façade surface has (not `[borrowed]`, not an external \
                             consumer); mark the slot `[manual]`",
                            func.name, arg.name
                        ));
                    }
                    let packed = format!("{}_frame", name);
                    lowered.params.push(format!("{}: &[impl AsRef<str>]", name));
                    lowered.prelude.push(format!(
                        "let {} = flowi_sys::fl_frame_str_array({}.len() as u32);",
                        packed, name
                    ));
                    lowered.prelude.push(format!(
                        "for (i, s) in {}.iter().enumerate() {{ let s = s.as_ref(); *{}.add(i) = \
                         flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()); }}",
                        name, packed
                    ));
                    lowered.ffi.push(packed);
                    lowered.ffi.push(format!("{}.len() as u32", name));
                    i += 1;
                    continue;
                }
                let elem_ty = Self::facade_slice_elem_type(surface, &arg.type_name);
                if arg.pointer {
                    lowered.params.push(format!("{}: &mut [{}]", name, elem_ty));
                    lowered.ffi.push(format!("{}.as_mut_ptr()", name));
                } else {
                    lowered.params.push(format!("{}: &[{}]", name, elem_ty));
                    lowered.ffi.push(format!("{}.as_ptr()", name));
                }
                lowered.ffi.push(format!("{}.len() as u32", name));
                i += 1;
                continue;
            }
            let (param, ffi, mut prelude) = Self::lower_loose_symbol_arg(surface, func, arg)?;
            if let Some(param) = param {
                lowered.params.push(param);
            }
            lowered.ffi.push(ffi);
            lowered.prelude.append(&mut prelude);
            i += 1;
        }
        Ok(lowered)
    }

    /// The String return needs no surface - the owned copy is an inherent method on
    /// the ABI string type, so it resolves through the receiver and both surfaces emit
    /// the same text. Every other classification names a generated type, which the two
    /// surfaces reach through different crate roots.
    fn lower_loose_symbol_result(
        surface: LooseSymbolSurface,
        func: &Function,
    ) -> Result<LoweredResult, String> {
        // Both out-param shapes below read their buffer back BY VALUE, through
        // MaybeUninit::assume_init. An extern opaque type is minted as a zero-variant
        // enum, which is uninhabited: no bit pattern is valid for it, so producing one is
        // undefined behaviour however faithfully the C side filled the buffer.
        if let Some(i) = Self::out_param_index(func) {
            let out = &func.function_args[i];
            if out.is_extern_opaque && (func.is_status || Self::is_option_shape(func)) {
                return Err(format!(
                    "slot `{}`: an out-param cannot be an `extern opaque` type -- `{}` is \
                     uninhabited in Rust, so reading it back by value is undefined behaviour. \
                     Return the pointer with `[transfer]`, or hand-write the slot.",
                    func.name, out.type_name
                ));
            }
        }
        if func.is_status {
            let valid = func
                .return_val
                .as_ref()
                .is_some_and(|r| !r.pointer && !r.const_pointer && r.vtype != VariableType::Str);
            if !valid {
                return Err(format!(
                    "slot `{}`: `[status]` requires an integer / enum / bool status return",
                    func.name
                ));
            }
            let out_idx = Self::out_param_index(func);
            return Ok(LoweredResult::Status {
                ok_ty: out_idx
                    .map(|i| Self::loose_symbol_base_type(surface, &func.function_args[i]))
                    .unwrap_or_else(|| "()".to_owned()),
                has_out: out_idx.is_some(),
            });
        }
        if Self::is_option_shape(func) {
            let i = Self::out_param_index(func).expect("option shape has out param");
            return Ok(LoweredResult::Option {
                ty: Self::loose_symbol_base_type(surface, &func.function_args[i]),
            });
        }
        if func.is_transfer {
            let ret = func.return_val.as_ref().ok_or_else(|| {
                format!(
                    "slot `{}`: `[transfer]` requires a pointer return",
                    func.name
                )
            })?;
            if !(ret.pointer || ret.const_pointer) || ret.type_name == "void" {
                return Err(format!(
                    "slot `{}`: a `[transfer]` return must be a pointer to a named type (got `{}`)",
                    func.name, ret.type_name
                ));
            }
            return Ok(LoweredResult::Transfer {
                owned_ty: Self::owned_newtype_name(&ret.type_name),
            });
        }
        let Some(ret) = &func.return_val else {
            return Ok(LoweredResult::Unit);
        };
        if ret.vtype == VariableType::Str {
            // A `[borrowed]` String return stays a view of the callee's bytes; the
            // wrapper's &self anchors its lifetime. Only the service wrapper has a
            // receiver - the stateless façade would let a caller infer 'static, so
            // there the return falls back to the owned copy below.
            if func.is_borrowed && surface != LooseSymbolSurface::DirectLink {
                return Ok(LoweredResult::Value {
                    ty: "&str".to_owned(),
                    wrap: Some("ret.as_str()".to_owned()),
                });
            }
            return Ok(LoweredResult::Value {
                ty: "String".to_owned(),
                wrap: Some("ret.into_string()".to_owned()),
            });
        }
        if ret.optional && (ret.pointer || ret.const_pointer) {
            return Err(format!(
                "optional-pointer return in `{}` cannot get a sound safe façade: no parameter \
                 carries the return reference's lifetime; mark the slot `[manual]`",
                func.name
            ));
        }
        if ret.pointer || ret.const_pointer {
            return Err(format!(
                "slot `{}`: unclassifiable raw-pointer return `{}`; add `[transfer(free = <slot>)]` \
                 for an owning handle, `[status]` for a `Result`, or mark the slot `[manual]`",
                func.name,
                Self::loose_symbol_ffi_type(surface, ret)
            ));
        }
        Ok(LoweredResult::Value {
            ty: Self::loose_symbol_base_type(surface, ret),
            wrap: None,
        })
    }

    fn write_comment<W: Write>(f: &mut W, comments: &[String], indent: usize) -> io::Result<()> {
        for c in comments {
            // A blank line inside a multi-paragraph doc block emits a bare ///
            // (no trailing space).
            if c.is_empty() {
                writeln!(f, "{:indent$}///", "", indent = indent)?;
            } else {
                writeln!(f, "{:indent$}/// {}", "", c, indent = indent)?;
            }
        }
        Ok(())
    }

    /// Rust spelling of a value's base type (no pointer qualifier): the string keyword
    /// crosses as crate::RawStr, primitives map through (void -> c_void, char
    /// -> c_char, the rest straight), and every other named type - including an
    /// opaque handle - is its unprefixed IDL name through the crate root
    /// (crate::Color).
    fn rust_base_type(var: &Variable) -> String {
        // An extern opaque dep is a module-local uninhabited ZST named by its
        // verbatim external C type (UiCtx, FlArena) - never crate::-qualified.
        if var.is_extern_opaque {
            return var.type_name.clone();
        }
        match var.vtype {
            VariableType::Str => "crate::RawStr".to_owned(),
            VariableType::Primitive => Self::ffi_primitive(&var.type_name),
            _ => format!("crate::{}", var.type_name),
        }
    }

    /// Rust spelling of an IDL primitive type name: the void/char C types map
    /// to their core::ffi equivalents, every other primitive passes through
    /// verbatim (f32, u64, ...).
    fn ffi_primitive(name: &str) -> String {
        match name {
            "void" => "core::ffi::c_void".to_owned(),
            "char" => "core::ffi::c_char".to_owned(),
            other => other.to_owned(),
        }
    }

    /// Apply a value's pointer qualifier to its base type (`*const T` / `*mut T`).
    fn apply_pointer(var: &Variable, base: String) -> String {
        if var.const_pointer {
            format!("*const {}", base)
        } else if var.pointer {
            format!("*mut {}", base)
        } else {
            base
        }
    }

    /// Rust spelling of any value - a struct field, union variant, method arg, or
    /// return - as the base type plus any pointer qualifier. A union field is
    /// special-cased by its caller, which names the generated union type instead.
    fn rust_field_type(var: &Variable) -> String {
        let base = Self::apply_pointer(var, Self::rust_base_type(var));
        match &var.array {
            // Unsized arrays are pointer+length args handled by the signature path.
            Some(ArrayType::SizedArray(n)) => format!("[{}; {}]", base, n),
            _ => base,
        }
    }

    /// Name of the generated Rust union type for an anonymous union field:
    /// `<struct name><Field>` (e.g. LayoutSizingAxis + size ->
    /// LayoutSizingAxisSize). Rust needs a named type for a `#[repr(C)]` union.
    fn union_type_name(struct_name: &str, field: &str) -> String {
        let mut out = struct_name.to_owned();
        let mut chars = field.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
        out
    }

    /// The Rust (field ident, type name) for a struct's union field. Rust has no
    /// anonymous union members, so a C anonymous union (field.name empty) gets a
    /// synthetic payload field of a `<Struct>Payload` union type; a named union keeps
    /// its own name and `<Struct><Field>` type.
    fn union_field_spelling(struct_name: &str, field: &Variable) -> (String, String) {
        if field.name.is_empty() {
            ("payload".to_owned(), format!("{}Payload", struct_name))
        } else {
            (
                Self::rust_ident(&field.name),
                Self::union_type_name(struct_name, &field.name),
            )
        }
    }

    /// Escape Rust keywords that can legally be raw identifiers (type -> `r#type`)
    /// so a C field name that collides with a keyword still emits valid Rust.
    ///
    /// self, super, and crate are path-relative keywords that rustc rejects as
    /// raw identifiers (`r#self` does not parse), so they take a trailing underscore
    /// (self_) instead. `#[repr(C)]` layout is field-name-independent, so the rename
    /// is ABI-neutral; the offset_of! guard names the same escaped ident.
    fn rust_ident(name: &str) -> String {
        match name {
            // Strict keywords plus the reserved-for-future-use set, across all editions
            // rather than the one the output is compiled at today (gen is reserved
            // from 2024 only): a missed one is a generated file that does not parse.
            "abstract" | "as" | "async" | "await" | "become" | "box" | "break" | "const"
            | "continue" | "do" | "dyn" | "else" | "enum" | "extern" | "false" | "final" | "fn"
            | "for" | "gen" | "if" | "impl" | "in" | "let" | "loop" | "macro" | "match" | "mod"
            | "move" | "mut" | "override" | "priv" | "pub" | "ref" | "return" | "static"
            | "struct" | "trait" | "true" | "try" | "type" | "typeof" | "unsafe" | "unsized"
            | "use" | "virtual" | "where" | "while" | "yield" => {
                format!("r#{}", name)
            }
            // The four the raw-identifier syntax does not accept.
            "self" | "Self" | "super" | "crate" => format!("{}_", name),
            _ => name.to_owned(),
        }
    }

    /// Emit a `#[repr(C)]` struct for a data type + its compile-time layout
    /// assertion, preceded by a named union type for each anonymous-union field.
    fn generate_data_struct<W: Write>(
        f: &mut W,
        sdef: &Struct,
        reg: &TypeRegistry,
    ) -> io::Result<()> {
        // Spelled by the unprefixed IDL name; the C side emits the matching real
        // typedef.
        let name = &sdef.name;

        // A union field needs a named Rust type, emitted (with its own size/align
        // guard) before the struct that embeds it.
        for var in &sdef.variables {
            if let Some(variants) = &var.union_variants {
                Self::generate_union(f, name, var, variants, reg)?;
            }
        }

        // The IDL layout the assertion pins (shared with the C-side guard).
        let layout = reg.layout_for(sdef);

        Self::write_comment(f, &sdef.doc_comments, 0)?;
        writeln!(f, "#[repr(C)]")?;
        // `#[attributes(Copy)]` gives the Copy/Clone set, plus Debug unless the struct
        // transitively embeds a union (which is not Debug). `#[attributes(Default)]`
        // adds a Default derive, so a config struct can be built with
        // ..Default::default() - the zeroed-config = "use the C defaults" convention.
        let mut derives: Vec<&str> = Vec::new();
        if sdef.has_attribute("Copy") {
            derives.push("Copy");
            derives.push("Clone");
            if !reg.contains_union(&sdef.name) {
                derives.push("Debug");
            }
        }
        if sdef.has_attribute("Default") {
            derives.push("Default");
        }
        if !derives.is_empty() {
            writeln!(f, "#[derive({})]", derives.join(", "))?;
        }
        writeln!(f, "pub struct {} {{", name)?;
        // Value + function fields in authored order: a vtable may carry a value field
        // after its function-pointers, and preserving the order matches the C struct
        // and the layout assertion below. A function-field mirrors as a nullable
        // `Option<unsafe extern "C" fn(args) -> ret>` slot - the null-pointer niche is
        // ABI-identical to a bare fn pointer; sized {8, 8} in layout.rs.
        for field in sdef.ordered_fields() {
            match field {
                FieldRef::Var(i) => {
                    let var = &sdef.variables[i];
                    Self::write_comment(f, &var.doc_comments, 4)?;
                    let (fname, ty) = if var.union_variants.is_some() {
                        Self::union_field_spelling(name, var)
                    } else {
                        (Self::rust_ident(&var.name), Self::rust_field_type(var))
                    };
                    writeln!(f, "    pub {}: {},", fname, ty)?;
                }
                FieldRef::Func(i) => {
                    let func = &sdef.functions[i];
                    Self::write_comment(f, &func.doc_comments, 4)?;
                    let (params, ret) = Self::rust_signature(func);
                    writeln!(
                        f,
                        "    pub {}: Option<unsafe extern \"C\" fn({}){}>,",
                        Self::rust_ident(&func.name),
                        params,
                        ret
                    )?;
                }
            }
        }
        writeln!(f, "}}")?;
        writeln!(f)?;

        Self::emit_layout_assert(f, name, &layout)?;
        Ok(())
    }

    /// Emit a `#[repr(C)]` union type for an anonymous union field, plus a
    /// size/align assertion pinning its IDL-computed layout.
    fn generate_union<W: Write>(
        f: &mut W,
        struct_name: &str,
        field: &Variable,
        variants: &[Variable],
        reg: &TypeRegistry,
    ) -> io::Result<()> {
        let (_, uname) = Self::union_field_spelling(struct_name, field);
        let sa = reg.union_size_align(variants);

        Self::write_comment(f, &field.doc_comments, 0)?;
        writeln!(f, "#[repr(C)]")?;
        writeln!(f, "#[derive(Copy, Clone)]")?;
        writeln!(f, "pub union {} {{", uname)?;
        for variant in variants {
            Self::write_comment(f, &variant.doc_comments, 4)?;
            writeln!(
                f,
                "    pub {}: {},",
                Self::rust_ident(&variant.name),
                Self::rust_field_type(variant)
            )?;
        }
        writeln!(f, "}}")?;
        writeln!(f)?;

        Self::emit_size_align_assert(f, uname.as_str(), sa.size, sa.align)?;
        Ok(())
    }

    /// Emit a `#[repr(C)]` enum for a data type (`#[repr(u8)]` for packed) + a
    /// size/align assertion.
    fn generate_data_enum<W: Write>(f: &mut W, edef: &Enum) -> io::Result<()> {
        // Spelled by the unprefixed IDL name; the C side emits the matching real
        // typedef.
        let name = &edef.name;
        let (size, align, repr) = if edef.is_packed {
            (1, 1, "u8")
        } else {
            (4, 4, "C")
        };

        Self::write_comment(f, &edef.doc_comments, 0)?;
        writeln!(f, "#[repr({})]", repr)?;
        writeln!(f, "#[derive(Copy, Clone, Debug, PartialEq, Eq)]")?;
        if edef.is_serde {
            writeln!(
                f,
                "#[cfg_attr(feature = \"serde\", derive(serde::Serialize, serde::Deserialize))]"
            )?;
        }
        writeln!(f, "pub enum {} {{", name)?;
        for entry in &edef.entries {
            Self::write_comment(f, &entry.doc_comments, 4)?;
            if let Some(value) = edef
                .entry_value_literal(entry)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
            {
                writeln!(f, "    {} = {},", entry.name, value)?;
            }
        }
        writeln!(f, "}}")?;
        writeln!(f)?;

        Self::emit_size_align_assert(f, name, size, align)?;
        Ok(())
    }

    /// Emit the inherent lookups a variant annotation asks for: `[label(...)]` on
    /// every variant gives `ALL`, `name`/`label` and their `from_*` inverses;
    /// any `[reserved]` variant gives `is_reserved`. Nothing for a plain enum.
    fn generate_enum_lookups<W: Write>(f: &mut W, edef: &Enum) -> io::Result<()> {
        let name = &edef.name;
        if let Some(labelled) = edef.labelled_entries() {
            writeln!(f, "impl {} {{", name)?;
            writeln!(f, "    /// Every variant, in declaration order.")?;
            writeln!(f, "    pub const ALL: [{}; {}] = [", name, labelled.len())?;
            for (entry, _) in &labelled {
                writeln!(f, "        {}::{},", name, entry.name)?;
            }
            writeln!(f, "    ];")?;
            writeln!(f)?;
            writeln!(f, "    /// The variant's name as the IDL spells it.")?;
            writeln!(f, "    #[must_use]")?;
            writeln!(f, "    pub const fn name(self) -> &'static str {{")?;
            writeln!(f, "        match self {{")?;
            for (entry, _) in &labelled {
                writeln!(
                    f,
                    "            {}::{} => \"{}\",",
                    name, entry.name, entry.name
                )?;
            }
            writeln!(f, "        }}")?;
            writeln!(f, "    }}")?;
            writeln!(f)?;
            writeln!(f, "    /// The variant's canonical display label.")?;
            writeln!(f, "    #[must_use]")?;
            writeln!(f, "    pub const fn label(self) -> &'static str {{")?;
            writeln!(f, "        match self {{")?;
            for (entry, label) in &labelled {
                writeln!(f, "            {}::{} => \"{}\",", name, entry.name, label)?;
            }
            writeln!(f, "        }}")?;
            writeln!(f, "    }}")?;
            writeln!(f)?;
            writeln!(f, "    /// The variant whose [`Self::name`] is `name`.")?;
            writeln!(f, "    #[must_use]")?;
            writeln!(f, "    pub fn from_name(name: &str) -> Option<Self> {{")?;
            writeln!(
                f,
                "        Self::ALL.into_iter().find(|v| v.name() == name)"
            )?;
            writeln!(f, "    }}")?;
            writeln!(f)?;
            writeln!(f, "    /// The variant whose [`Self::label`] is `label`.")?;
            writeln!(f, "    #[must_use]")?;
            writeln!(f, "    pub fn from_label(label: &str) -> Option<Self> {{")?;
            writeln!(
                f,
                "        Self::ALL.into_iter().find(|v| v.label() == label)"
            )?;
            writeln!(f, "    }}")?;
            writeln!(f, "}}")?;
            writeln!(f)?;
        }
        if let Some(reserved) = edef.reserved_entries() {
            let pattern: Vec<String> = reserved
                .iter()
                .map(|entry| format!("{}::{}", name, entry.name))
                .collect();
            writeln!(f, "impl {} {{", name)?;
            writeln!(
                f,
                "    /// Whether this variant is reserved to the side that owns the enum."
            )?;
            writeln!(f, "    #[must_use]")?;
            writeln!(f, "    pub const fn is_reserved(self) -> bool {{")?;
            writeln!(f, "        matches!(self, {})", pattern.join(" | "))?;
            writeln!(f, "    }}")?;
            writeln!(f, "}}")?;
            writeln!(f)?;
        }
        Ok(())
    }

    /// Emit the shared FlError companion of an `#[attributes(error_enum)]`
    /// status enum: one variant per non-success code (success = the code-0
    /// entry, which becomes the Ok arm of the decode) plus an Unknown(i32)
    /// catch-all, with from_status/from_code decode impls and
    /// Display/Error. Rust-side only - the C surface keeps the plain status
    /// enum.
    fn generate_error_enum<W: Write>(f: &mut W, edef: &Enum) -> io::Result<()> {
        let status = &edef.name;
        let invalid = |msg: String| io::Error::new(io::ErrorKind::InvalidData, msg);

        // Every entry needs an explicit resolved value: the decode match arms
        // are spelled from them, and the success code must be identifiable.
        let mut entries: Vec<(&EnumEntry, String)> = Vec::new();
        for entry in &edef.entries {
            let value = edef
                .entry_value_literal(entry)
                .map_err(invalid)?
                .ok_or_else(|| {
                    invalid(format!(
                        "error_enum `{}`: entry `{}` needs an explicit value",
                        status, entry.name
                    ))
                })?;
            entries.push((entry, value));
        }
        let success = entries
            .iter()
            .find(|(_, v)| v == "0")
            .map(|(e, _)| e.name.clone())
            .ok_or_else(|| invalid(format!("error_enum `{}`: no code-0 success entry", status)))?;
        entries.retain(|(_, v)| v != "0");

        writeln!(
            f,
            "/// A failed flowi operation: every non-success [`{status}`] code as a named\n\
             /// variant. Ok/success ({status}::{success}, code 0) is never an FlError;\n\
             /// it is the Ok arm of the Result these decode into. A code outside the\n\
             /// known set decodes to [`FlError::Unknown`] carrying the raw value - a host\n\
             /// newer than these bindings is preserved, never panicked on."
        )?;
        writeln!(f, "#[derive(Debug, Clone, Copy, PartialEq, Eq)]")?;
        writeln!(f, "pub enum FlError {{")?;
        for (entry, _) in &entries {
            Self::write_comment(f, &entry.doc_comments, 4)?;
            writeln!(f, "    {},", entry.name)?;
        }
        writeln!(
            f,
            "    /// A status code outside the known [`{status}`] set - carries the raw code\n\
             \x20   /// so a newer host's additions survive round-tripping rather than being\n\
             \x20   /// lost."
        )?;
        writeln!(f, "    Unknown(i32),")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        writeln!(f, "impl FlError {{")?;
        writeln!(
            f,
            "    /// Decode a raw C status code into a Result: 0 ({status}::{success}) is\n\
             \x20   /// Ok(()), every other code is the matching Err(FlError)."
        )?;
        writeln!(f, "    #[inline]")?;
        writeln!(
            f,
            "    pub fn from_status(code: i32) -> Result<(), FlError> {{"
        )?;
        writeln!(f, "        match code {{")?;
        writeln!(f, "            0 => Ok(()),")?;
        writeln!(f, "            other => Err(FlError::from_code(other)),")?;
        writeln!(f, "        }}")?;
        writeln!(f, "    }}")?;
        writeln!(f)?;
        writeln!(
            f,
            "    /// Map a status code to its variant. 0 and any unrecognised code decode to\n\
             \x20   /// [`FlError::Unknown`] - this never panics, whatever the host sends."
        )?;
        writeln!(f, "    pub fn from_code(code: i32) -> FlError {{")?;
        writeln!(f, "        match code {{")?;
        for (entry, value) in &entries {
            writeln!(f, "            {} => FlError::{},", value, entry.name)?;
        }
        writeln!(f, "            other => FlError::Unknown(other),")?;
        writeln!(f, "        }}")?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        writeln!(f, "impl std::fmt::Display for FlError {{")?;
        writeln!(
            f,
            "    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {{"
        )?;
        writeln!(f, "        match self {{")?;
        writeln!(
            f,
            "            FlError::Unknown(code) => write!(f, \"unknown flowi status code {{code}}\"),"
        )?;
        writeln!(
            f,
            "            other => write!(f, \"flowi error: {{other:?}}\"),"
        )?;
        writeln!(f, "        }}")?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;
        writeln!(f, "impl std::error::Error for FlError {{}}")?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit a bitflags enum: a bitflags! set over the type's width, spelled by
    /// the unprefixed IDL name, with each variant a SHOUTY const.
    /// `#[repr(transparent)]` over the u32 fixes the width; the const _ pins it.
    fn generate_bitflags<W: Write>(f: &mut W, edef: &Enum) -> io::Result<()> {
        let name = &edef.name;

        // The doc comment lives inside the macro, on the generated struct -
        // rustdoc does not attach a doc comment to the macro invocation itself.
        writeln!(f, "bitflags::bitflags! {{")?;
        Self::write_comment(f, &edef.doc_comments, 4)?;
        writeln!(f, "    #[repr(transparent)]")?;
        // Default is the empty set, which lets a flag field sit in a struct
        // that derives Default.
        writeln!(
            f,
            "    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]"
        )?;
        writeln!(f, "    pub struct {}: u32 {{", name)?;
        for entry in &edef.entries {
            Self::write_comment(f, &entry.doc_comments, 8)?;
            if let Some(value) = edef
                .entry_value_literal(entry)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
            {
                writeln!(
                    f,
                    "        const {} = {};",
                    entry.name.to_shouty_snake_case(),
                    value
                )?;
            }
        }
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        Self::emit_size_assert(f, name, 4)?;
        Ok(())
    }

    /// Emit the const _ layout assertion for a struct against the IDL-computed
    /// constants. If anyone hand-edits the struct, this stops compiling.
    fn emit_layout_assert<W: Write>(
        f: &mut W,
        name: &str,
        layout: &crate::layout::StructLayout,
    ) -> io::Result<()> {
        writeln!(f, "const _: () = {{")?;
        writeln!(
            f,
            "    assert!(core::mem::size_of::<{}>() == {}, \"{} size drift\");",
            name, layout.size, name
        )?;
        writeln!(
            f,
            "    assert!(core::mem::align_of::<{}>() == {}, \"{} align drift\");",
            name, layout.align, name
        )?;
        for fl in &layout.fields {
            // An anonymous union member has no name; it is spelled payload on the
            // Rust side (see union_field_spelling), so pin its offset under that name.
            let field = if fl.name.is_empty() {
                "payload"
            } else {
                &fl.name
            };
            writeln!(
                f,
                "    assert!(core::mem::offset_of!({}, {}) == {}, \"{}.{} offset drift\");",
                name,
                Self::rust_ident(field),
                fl.offset,
                name,
                field
            )?;
        }
        writeln!(f, "}};")?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit a standalone const _ block pinning a type's size and alignment - the
    /// scalar counterpart to emit_layout_assert (which additionally pins each
    /// field's offset). Used for enums and union types, whose layout has no fields
    /// to offset-check.
    fn emit_size_align_assert<W: Write>(
        f: &mut W,
        name: &str,
        size: impl std::fmt::Display,
        align: impl std::fmt::Display,
    ) -> io::Result<()> {
        writeln!(f, "const _: () = {{")?;
        writeln!(
            f,
            "    assert!(core::mem::size_of::<{}>() == {}, \"{} size drift\");",
            name, size, name
        )?;
        writeln!(
            f,
            "    assert!(core::mem::align_of::<{}>() == {}, \"{} align drift\");",
            name, align, name
        )?;
        writeln!(f, "}};")?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit a standalone const _ block pinning only a type's size - for the
    /// width-fixed cases (a `#[repr(transparent)]` bitflags set or handle newtype)
    /// where alignment follows the underlying integer and needs no separate assert.
    fn emit_size_assert<W: Write>(
        f: &mut W,
        name: &str,
        size: impl std::fmt::Display,
    ) -> io::Result<()> {
        writeln!(f, "const _: () = {{")?;
        writeln!(
            f,
            "    assert!(core::mem::size_of::<{}>() == {}, \"{} size drift\");",
            name, size, name
        )?;
        writeln!(f, "}};")?;
        writeln!(f)?;
        Ok(())
    }

    /// Signature fragment name: Type, ... for a method's non-self args, plus the ` -> Ret` suffix.
    fn rust_signature(func: &Function) -> (String, String) {
        Self::rust_sig_parts(&func.function_args, func.return_val.as_ref())
    }

    /// Signature fragment from a bare arg list + optional return - the shared core
    /// of [`rust_signature`], reused by callback aliases (same shape, no
    /// enclosing Function). Self args are filtered out; callbacks carry none.
    fn rust_sig_parts(args: &[Variable], ret: Option<&Variable>) -> (String, String) {
        let params = args
            .iter()
            .filter(|a| a.vtype != VariableType::SelfType)
            .map(|a| {
                // An `[*const T]` array arg crosses the ABI as a raw pointer plus an auto `<name>_size: u32`
                // length companion - the sys-extern mirror of the C `T*, uint32_t <name>_size` lowering.
                if matches!(a.array, Some(ArrayType::Unsized)) {
                    let base = Self::rust_base_type(a);
                    let ptr = if a.pointer {
                        format!("*mut {}", base)
                    } else {
                        format!("*const {}", base)
                    };
                    format!("{}: {}, {}_size: u32", a.name, ptr, a.name)
                } else {
                    format!("{}: {}", a.name, Self::rust_field_type(a))
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let ret = match ret {
            Some(v) => format!(" -> {}", Self::rust_field_type(v)),
            None => String::new(),
        };
        (params, ret)
    }

    /// Emit a `callback <Name>` construct as a Rust fn-pointer type alias:
    /// `pub type <Name> = Option<unsafe extern "C" fn(args) -> ret>;`. The Option is
    /// the null-pointer niche, ABI-identical to a bare fn pointer for the non-null
    /// case, matching the nullable struct fn-field mirror. Spelled by the unprefixed
    /// IDL name; the C side emits the matching typedef.
    fn generate_callback_alias<W: Write>(f: &mut W, cb: &Callback) -> io::Result<()> {
        Self::write_comment(f, &cb.doc_comments, 0)?;
        let (params, ret) = Self::rust_sig_parts(&cb.function_args, cb.return_val.as_ref());
        writeln!(
            f,
            "pub type {} = Option<unsafe extern \"C\" fn({}){}>;",
            cb.name, params, ret
        )?;
        writeln!(f)?;
        Ok(())
    }

    /// `mod <name>` deps: bring each hand-written public module's types into scope so
    /// a generated signature can name a read-payload type one of them defines. Mirrors
    /// the C header's `#include` of the same header; unused_imports is allowed since
    /// not every binding in a def names one.
    fn generate_mod_imports<W: Write>(f: &mut W, api_def: &ApiDef) -> io::Result<()> {
        for m in &api_def.mods {
            writeln!(f, "#[allow(unused_imports)]")?;
            writeln!(f, "use crate::{}::*;", m)?;
        }
        if !api_def.mods.is_empty() {
            writeln!(f)?;
        }
        Ok(())
    }

    /// A generated file's leading comment block: the do-not-edit banner, plus the
    /// shared //! SAFETY: statement when body actually contains an unsafe block.
    fn generated_header(body: &str, script: &str) -> String {
        Self::generated_header_with(body, &[], script)
    }

    /// [`generated_header`] plus backend-specific inner attributes, emitted alongside
    /// the shared //! SAFETY: statement and under the same condition - they qualify
    /// unsafe the generator wrote, so a file with none of it needs none of them.
    fn generated_header_with(body: &str, extra_attrs: &[&str], script: &str) -> String {
        let mut header = format!("{}\n", crate::emit_util::header(script));
        if body.contains("unsafe {") {
            header.push_str(RUST_GENERATED_SAFETY_HEADER);
            for attr in extra_attrs {
                header.push_str(attr);
                header.push('\n');
            }
            header.push('\n');
        }
        header
    }

    pub fn generate(
        rust_dir: &str,
        api_def: &ApiDef,
        reg: &TypeRegistry,
        script: &str,
    ) -> io::Result<()> {
        let filename = format!("{}/{}.rs", rust_dir, api_def.base_filename);
        let mut f = BufWriter::new(File::create(&filename)?);

        write!(f, "{}", crate::emit_util::header(script))?;
        writeln!(f)?;

        Self::generate_mod_imports(&mut f, api_def)?;

        // `#[const]` constants emit as pub const (u64), mirroring the C header's
        // `#define`.
        for (name, value) in &api_def.consts {
            writeln!(f, "pub const {}: u64 = {};", name, value)?;
        }
        if !api_def.consts.is_empty() {
            writeln!(f)?;
        }

        for enum_def in &api_def.enums {
            if enum_def.enum_type == EnumType::Bitflags {
                Self::generate_bitflags(&mut f, enum_def)?;
            } else {
                Self::generate_data_enum(&mut f, enum_def)?;
                Self::generate_enum_lookups(&mut f, enum_def)?;
            }
            // An `#[attributes(error_enum)]` status enum also emits the shared
            // FlError companion into the same module.
            if enum_def.is_error_enum {
                Self::generate_error_enum(&mut f, enum_def)?;
            }
        }

        // extern opaque deps: a module-local uninhabited enum per dep, emitted before
        // the structs that name them.
        for ext in &api_def.externs {
            Self::generate_extern_opaque_type(&mut f, ext)?;
        }

        // `callback <Name>` aliases - emitted after the extern-opaque ZSTs they may
        // name and before the structs, so a struct field may reference the alias.
        for cb in &api_def.callbacks {
            Self::generate_callback_alias(&mut f, cb)?;
        }

        for sdef in &api_def.structs {
            if sdef.is_handle_type {
                Self::generate_handle_newtype(&mut f, sdef)?;
            } else if sdef.is_opaque() {
                Self::generate_opaque_type(&mut f, sdef)?;
            } else {
                Self::generate_data_struct(&mut f, sdef, reg)?;
            }
        }

        // Emitted after the domain's data types so the signatures can name them. A
        // `#[attributes(service)]` block is no different - it declares the same
        // extern "C" block, its slots linking the raw exported symbols.
        for api in &api_def.apis {
            Self::generate_api_externs(&mut f, api)?;
        }

        Ok(())
    }

    /// Emit an `api <Domain>` block as an extern "C" block declaring its direct
    /// `fl_*` functions - the ABI entry points the ergonomic façade forwards to.
    /// Args and return spell through rust_signature, exactly as the C prototype
    /// spells through c_value_type, so the two stay ABI-identical. Varargs slots
    /// are skipped: stable Rust cannot call a C variadic, so C reaches them
    /// through the `FL_<DOMAIN>_<FN>` macro. `[c_only]` slots are skipped too.
    fn generate_api_externs<W: Write>(f: &mut W, api: &Api) -> io::Result<()> {
        let mut funcs = api
            .functions
            .iter()
            .filter(|func| !func.has_varargs && !func.is_c_only)
            .peekable();
        if funcs.peek().is_none() {
            // A domain with only varargs slots has no Rust-callable surface.
            return Ok(());
        }

        // The domain doc rides as a plain // block - rustdoc does not attach a ///
        // doc comment to an extern block (it would warn).
        for c in &api.doc_comments {
            if c.is_empty() {
                writeln!(f, "//")?;
            } else {
                writeln!(f, "// {}", c)?;
            }
        }
        writeln!(f, "extern \"C\" {{")?;
        for func in funcs {
            let (params, ret) = Self::rust_signature(func);
            Self::write_comment(f, &func.doc_comments, 4)?;
            writeln!(f, "    pub fn {}({}){};", func.c_name, params, ret)?;
        }
        writeln!(f, "}}")?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit a handle as a `#[repr(transparent)]` newtype over its underlying
    /// integer, plus an INVALID sentinel const and a size assertion. The IDL
    /// integer name (u32) is the Rust field type directly; the sentinel value is
    /// spelled verbatim. A bare `#[attributes(Handle)]` (no `#[handle(...)]` spec)
    /// keeps the legacy u64 newtype with no sentinel.
    fn generate_handle_newtype<W: Write>(f: &mut W, sdef: &Struct) -> io::Result<()> {
        Self::write_comment(f, &sdef.doc_comments, 0)?;
        let name = &sdef.name;
        writeln!(f, "#[repr(transparent)]")?;
        writeln!(f, "#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]")?;
        match &sdef.handle {
            Some(spec) => {
                writeln!(f, "pub struct {}(pub {});", name, spec.int_type)?;
                writeln!(f)?;
                writeln!(f, "impl {} {{", name)?;
                writeln!(f, "    /// The invalid / \"none\" sentinel.")?;
                writeln!(f, "    pub const INVALID: Self = Self({});", spec.invalid)?;
                writeln!(f, "}}")?;
                writeln!(f)?;
                let size = crate::layout::type_size_align(&spec.int_type)
                    .map(|sa| sa.size)
                    .unwrap_or(8);
                Self::emit_size_assert(f, name, size)?;
            }
            None => {
                writeln!(f, "pub struct {}(pub u64);", name)?;
                writeln!(f)?;
            }
        }
        Ok(())
    }

    /// Emit an opaque type as an uninhabited (zero-variant) enum - the canonical
    /// Rust FFI spelling for a C forward-declared struct, nameable only behind a
    /// pointer (`*mut TextInputState`).
    fn generate_opaque_type<W: Write>(f: &mut W, sdef: &Struct) -> io::Result<()> {
        Self::write_comment(f, &sdef.doc_comments, 0)?;
        writeln!(f, "pub enum {} {{}}", sdef.name)?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit an extern opaque dep as a module-local uninhabited enum, spelled by its
    /// verbatim external C type (UiCtx, FlArena) - named verbatim, with no
    /// prefix drop, because the dep is external rather than IDL-authored.
    fn generate_extern_opaque_type<W: Write>(f: &mut W, ext: &ExternType) -> io::Result<()> {
        Self::write_comment(f, &ext.doc_comments, 0)?;
        writeln!(f, "pub enum {} {{}}", ext.name)?;
        writeln!(f)?;
        Ok(())
    }

    // ---- Ergonomic façade (flowi crate) -----------------------------------
    //
    // For each `api <Domain>` block: `pub struct <Domain>; impl <Domain> { ... }` into
    // the flowi crate (`rust/flowi/src/generated/<def>.rs`), each method forwarding
    // to `flowi_sys::<fl_domain_slot>(ffi...)`. `[manual]` and varargs slots are
    // skipped - the hand-written wrapper stays.

    /// Base façade spelling of a value's type, no pointer qualifier. Strings are
    /// handled by the caller (`impl AsRef<str>`); every generated data type / enum /
    /// handle is spelled `flowi_sys::<Name>`, which side-steps a re-export clash
    /// between a domain façade struct and a same-named data type (e.g. Cursor).
    fn facade_base_type(var: &Variable) -> String {
        Self::loose_symbol_base_type(LooseSymbolSurface::DirectLink, var)
    }

    /// How a referring signature spells a mirrored struct's safe twin:
    /// `crate::generated::<module>::<Name>`, plus an anonymous borrow when the twin
    /// carries one. The twin lives in the façade module of the def that declares it,
    /// which is not necessarily the def whose slot takes it.
    fn mirror_ref_path(type_name: &str, mirror: &MirrorRef) -> String {
        Self::mirror_path(type_name, mirror, "'_")
    }

    /// The twin's path with an explicit borrow spelling - '_ for a signature that
    /// elides it, 'a for a nested field inside another twin, which must name the
    /// enclosing struct's parameter.
    fn mirror_path(type_name: &str, mirror: &MirrorRef, lifetime: &str) -> String {
        let lifetime = if mirror.lifetime {
            format!("<{}>", lifetime)
        } else {
            String::new()
        };
        format!(
            "crate::generated::{}::{}{}",
            mirror.module, type_name, lifetime
        )
    }

    /// Façade method name for a slot: the slot name with a trailing _impl
    /// dropped (a C body-name suffix that should not leak into the Rust API, e.g.
    /// the menu domain's begin_impl -> begin). Otherwise verbatim.
    fn facade_method_name(slot: &str) -> &str {
        slot.strip_suffix("_impl").unwrap_or(slot)
    }

    /// The Rust façade spelling of a `[slice(T)]` / `[slice_mut(T)]` element type T:
    /// a primitive maps through (u64, core::ffi::c_void for void), every
    /// generated mirror is reached through the surface's crate root.
    fn facade_slice_elem_type(surface: LooseSymbolSurface, name: &str) -> String {
        let root = Self::loose_symbol_crate_root(surface);
        if is_primitive(name) {
            Self::ffi_primitive(name)
        } else if name == "String" {
            // String is the IDL keyword for an FlString, whose ABI mirror is the
            // hand-packed RawStr. Both the scalar arg and the `[*const String]` array
            // sidestep this, so it is reached only by an explicitly
            // `[slice(String)]`-marked raw slot.
            format!("{}::RawStr", root)
        } else {
            format!("{}::{}", root, name)
        }
    }

    /// Lower a slot's args into parallel (rust_params, ffi_exprs, prelude) vectors,
    /// applying every per-arg façade conversion in one place. handle is the RAII
    /// receiver arg, threaded as self.handle and contributing no param (None for
    /// the stateless façade paths). out_idx names a trailing `*mut T` out-param the
    /// caller handles: it crosses as out.as_mut_ptr() and contributes no visible
    /// parameter. prelude is statements the method body runs (inside its unsafe
    /// block) before the slot call - the `[retained]` copy-into-owned-storage
    /// lowering; empty otherwise.
    fn facade_args(
        func: &Function,
        handle: Option<&str>,
        out_idx: Option<usize>,
    ) -> (Vec<String>, Vec<String>, Vec<String>) {
        let lowered =
            Self::lower_loose_symbol_args(LooseSymbolSurface::DirectLink, func, handle, out_idx)
                .unwrap_or_else(|diag| panic!("{}", diag));
        (lowered.params, lowered.ffi, lowered.prelude)
    }

    /// Façade return spelling: (type_after_arrow, wrap), or None for a ()
    /// return. wrap turns the raw slot result ret into the ergonomic value.
    ///
    /// An optional-pointer return (`*const T?` / `*T?`) is rejected outright: the
    /// safe spelling would be `Option<&'a T>`, but no façade parameter carries 'a
    /// (façades are static methods on ZST domain structs), so a caller could infer
    /// 'static and hold the reference past the C-owned pointee's real lifetime.
    fn facade_return(func: &Function) -> Option<(String, String)> {
        match Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
            .unwrap_or_else(|diag| panic!("{}", diag))
        {
            LoweredResult::Unit => None,
            LoweredResult::Value { ty, wrap } => {
                Some((ty, wrap.unwrap_or_else(|| "ret".to_owned())))
            }
            other => panic!(
                "slot `{}` reached plain façade return emission with {:?}",
                func.name, other
            ),
        }
    }

    /// Whether a slot takes an extern opaque dep. The dep is
    /// generated as an uninhabited enum, so a safe &mut/& to it can never
    /// be produced - a façade method taking one would type-check but have no
    /// legal caller. Such slots stay raw-FFI-only in flowi_sys.
    fn has_extern_opaque_arg(func: &Function) -> bool {
        func.function_args.iter().any(|a| a.is_extern_opaque)
    }

    /// Whether a slot gets a generated façade method: skip the hand-written
    /// (`[manual]`), the varargs slots (inexpressible / bespoke), `[c_only]`
    /// slots (no Rust consumer), and slots taking an extern opaque dep
    /// (uncallable from safe code).
    fn facade_generates(func: &Function) -> bool {
        func.func_type != FunctionType::Manual
            && !func.has_varargs
            && !func.is_c_only
            && !Self::has_extern_opaque_arg(func)
    }

    /// Resolve a slot's façade call into (return type, unsafe-block tail):
    /// (None, call) for a () return, the call itself when the raw result passes
    /// through, or `let ret = <call>; <wrap>` when it needs wrapping. A wrap touches
    /// the raw slot result, so the binding and the wrap share one unsafe block.
    fn facade_call_expr(func: &Function, call: String) -> (Option<String>, String) {
        match Self::facade_return(func) {
            None => (None, call),
            Some((ret_ty, wrap)) => {
                if wrap == "ret" {
                    (Some(ret_ty), call)
                } else {
                    (Some(ret_ty), format!("let ret = {}; {}", call, wrap))
                }
            }
        }
    }

    /// Number of parameters in a rendered signature fragment. Generated types nest
    /// (`Option<&'a T>`, `impl Into<crate::LayoutId>`), so commas inside angle
    /// brackets do not separate parameters.
    fn param_count(params: &str) -> usize {
        if params.trim().is_empty() {
            return 0;
        }
        let mut depth = 0i32;
        let mut count = 1;
        let mut prev = ' ';
        for c in params.chars() {
            match c {
                '<' | '(' | '[' => depth += 1,
                // The `>` of a callback's `-> Ret` closes nothing.
                '>' if prev == '-' => {}
                '>' | ')' | ']' => depth -= 1,
                ',' if depth == 0 => count += 1,
                _ => {}
            }
            prev = c;
        }
        count
    }

    /// Shared skeleton of every generated façade method: `#[inline]`, the
    /// `pub fn <method>(<params>)[ -> <ret>]` signature line, body for the braced
    /// block's contents, closing brace.
    fn write_facade_method<W: Write>(
        f: &mut W,
        method: &str,
        params: &str,
        ret_ty: Option<&str>,
        body: impl FnOnce(&mut W) -> io::Result<()>,
    ) -> io::Result<()> {
        // A forwarder's arity is the C prototype's, so clippy's argument-count advice
        // has nothing to act on here - the fix would be an IDL change, not a codegen one.
        if Self::param_count(params) > CLIPPY_MAX_ARGS {
            writeln!(f, "    #[allow(clippy::too_many_arguments)]")?;
        }
        writeln!(f, "    #[inline]")?;
        match ret_ty {
            None => writeln!(f, "    pub fn {}({}) {{", method, params)?,
            Some(ret) => writeln!(f, "    pub fn {}({}) -> {} {{", method, params, ret)?,
        }
        body(f)?;
        writeln!(f, "    }}")
    }

    /// The safe twin's spelling of one mirrored field, over the shapes the parser's
    /// validate_mirror_struct admits: a scalar string becomes a plain &'a str, an
    /// optional const pointer an `Option<&'a T>`, a nested mirrored config its own
    /// twin, a mutable pointer to an opaque type the raw pointer, and everything else
    /// passes through as the ABI type.
    fn mirror_field_type(var: &Variable) -> String {
        if var.vtype == VariableType::Str {
            return "&'a str".to_owned();
        }
        if let Some(nested) = Self::mirror_field_nested(var) {
            return Self::mirror_path(&var.type_name, nested, "'a");
        }
        let base = Self::facade_base_type(var);
        if var.const_pointer {
            format!("Option<&'a {}>", base)
        } else if var.pointer {
            format!("*mut {}", base)
        } else {
            base
        }
    }

    /// The twin of a by-value field that is itself a mirrored config, or None for
    /// every other field shape. A pointer field is never lowered through the nested
    /// twin even when it points at a mirrored type: the twin is a by-value lowering.
    fn mirror_field_nested(var: &Variable) -> Option<&MirrorRef> {
        if var.pointer || var.const_pointer {
            return None;
        }
        var.mirror.as_ref()
    }

    /// The safe twin's Default value for one mirrored field: the declared `= value`
    /// of a bool or numeric field, else the C zero default, spelled safely. A
    /// pass-through field is read out of the zeroed ABI struct the emitter binds as
    /// zero, which is how a field of any scalar shape gets its zero without the
    /// generator needing a per-type literal.
    fn mirror_field_default(var: &Variable) -> String {
        if let Some(literal) = Self::mirror_declared_default(var) {
            literal
        } else if var.vtype == VariableType::Str {
            "\"\"".to_owned()
        } else if Self::mirror_field_nested(var).is_some() {
            // The nested twin's own Default, so the whole tree still reproduces
            // (FlConfig){0}.
            "Default::default()".to_owned()
        } else if var.const_pointer {
            "None".to_owned()
        } else if var.pointer {
            "core::ptr::null_mut()".to_owned()
        } else {
            format!("zero.{}", Self::rust_ident(&var.name))
        }
    }

    /// The Rust literal for a by-value bool or numeric field's declared `= value`,
    /// if it has one. An integer literal on a float field gains a `.0`.
    fn mirror_declared_default(var: &Variable) -> Option<String> {
        if var.default_value.is_empty()
            || var.vtype != VariableType::Primitive
            || var.pointer
            || var.const_pointer
            || var.array.is_some()
        {
            return None;
        }
        let value = var.default_value.as_str();
        match var.type_name.as_str() {
            "bool" if value == "true" || value == "false" => Some(value.to_owned()),
            "f32" | "f64" if value.parse::<f64>().is_ok() => Some(if value.contains('.') {
                value.to_owned()
            } else {
                format!("{value}.0")
            }),
            "bool" | "f32" | "f64" | "char" | "void" => None,
            _ if value.parse::<i128>().is_ok() => Some(value.to_owned()),
            _ => None,
        }
    }

    /// Lower one mirrored field back to its ABI spelling inside to_sys. A string is
    /// copied into the per-frame arena; an optional reference becomes a pointer or
    /// null; everything else is Copy and passes through.
    fn mirror_field_to_sys(var: &Variable) -> String {
        let name = Self::rust_ident(&var.name);
        if var.vtype == VariableType::Str {
            Self::arena_str_expr(&format!("self.{}", name))
        } else if Self::mirror_field_nested(var).is_some() {
            format!("self.{}.to_sys()", name)
        } else if var.const_pointer {
            format!(
                "self.{}.map_or(core::ptr::null(), |v| v as *const {})",
                name,
                Self::facade_base_type(var)
            )
        } else {
            format!("self.{}", name)
        }
    }

    /// Emit the safe twin of a `#[attributes(Mirror)]` config struct: the struct
    /// itself, its Default (the C zero default), and the crate-private to_sys
    /// the generated façade slots call.
    ///
    /// to_sys copies each string field into the per-frame arena (inline
    /// flowi_sys::fl_frame_str), so the FlString it hands C is valid for the rest
    /// of the current frame and no longer. A mirrored string field must therefore be
    /// one C either reads during the call or keeps no longer than the frame; a field a
    /// C consumer stores across frames needs a longer-lived allocation and must not be
    /// mirrored this way.
    fn generate_mirror_struct<W: Write>(f: &mut W, sdef: &Struct) -> io::Result<()> {
        // Borrowing is transitive through a nested twin: a config whose only string
        // lives in the WidgetConfig it embeds still carries the borrow. The parser
        // resolved that when it annotated the field, so read it back off the field.
        let lifetime = if sdef.variables.iter().any(|v| {
            v.vtype == VariableType::Str
                || v.const_pointer
                || Self::mirror_field_nested(v).is_some_and(|m| m.lifetime)
        }) {
            "<'a>"
        } else {
            ""
        };
        // The elided form the impl blocks use; Default and to_sys never name the
        // borrow, so '_ keeps them free of an unused parameter.
        let elided = if lifetime.is_empty() { "" } else { "<'_>" };

        Self::write_comment(f, &sdef.doc_comments, 0)?;
        writeln!(f, "///")?;
        writeln!(
            f,
            "/// The safe twin of [`flowi_sys::{}`]: each FlString field is a plain &str and each optional",
            sdef.name
        )?;
        writeln!(
            f,
            "/// pointer an `Option<&T>`, so the whole config is constructible from safe code with no"
        )?;
        writeln!(
            f,
            "/// flowi_sys import. Build one with ..Default::default() - [`Default`] is the C zero default -"
        )?;
        writeln!(
            f,
            "/// and pass it to any façade slot taking this config; the strings are copied into the per-frame"
        )?;
        writeln!(
            f,
            "/// arena at the call, so temporaries (a format! result) are fine."
        )?;
        // Debug is deliberately absent: a pointer field's pointee is an ABI mirror
        // that need not derive it, so requiring it would make the twin's derive set
        // depend on an unrelated type's.
        writeln!(f, "#[derive(Copy, Clone)]")?;
        writeln!(f, "pub struct {}{} {{", sdef.name, lifetime)?;
        for var in &sdef.variables {
            Self::write_comment(f, &var.doc_comments, 4)?;
            writeln!(
                f,
                "    pub {}: {},",
                Self::rust_ident(&var.name),
                Self::mirror_field_type(var)
            )?;
        }
        writeln!(f, "}}")?;
        writeln!(f)?;

        // The zeroed ABI struct is only bound when a field actually reads a scalar out
        // of it; a config whose every field is a string, a pointer, or a nested twin
        // would otherwise bind it unused.
        let needs_zero = sdef
            .variables
            .iter()
            .any(|var| Self::mirror_field_default(var).starts_with("zero."));

        writeln!(f, "impl Default for {}{} {{", sdef.name, elided)?;
        writeln!(f, "    #[inline]")?;
        writeln!(f, "    fn default() -> Self {{")?;
        writeln!(
            f,
            "        // Each field takes the default its .def declares, else the C zero default ((Fl{}){{0}}): empty",
            sdef.name
        )?;
        writeln!(
            f,
            "        // strings, no optional pointers, and zero scalars - including each nested config, whose own Default is"
        )?;
        writeln!(f, "        // that struct's C zero default.")?;
        if needs_zero {
            writeln!(
                f,
                "        // SAFETY: flowi_sys::{} is a `#[repr(C)]` plain-data mirror of the C struct, whose",
                sdef.name
            )?;
            writeln!(
                f,
                "        // all-zero value is its documented default; api_gen checks every by-value field admits"
            )?;
            writeln!(
                f,
                "        // that bit pattern (each enum field has a 0-valued variant)."
            )?;
            writeln!(
                f,
                "        let zero: flowi_sys::{} = unsafe {{ core::mem::zeroed() }};",
                sdef.name
            )?;
        }
        writeln!(f, "        {} {{", sdef.name)?;
        for var in &sdef.variables {
            writeln!(
                f,
                "            {}: {},",
                Self::rust_ident(&var.name),
                Self::mirror_field_default(var)
            )?;
        }
        writeln!(f, "        }}")?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        writeln!(f, "impl {}{} {{", sdef.name, elided)?;
        writeln!(
            f,
            "    /// Lower to the ABI struct the C seam takes, copying each string into the per-frame arena."
        )?;
        writeln!(
            f,
            "    /// The result borrows that arena, so it is valid for the rest of the current frame - pass it"
        )?;
        writeln!(f, "    /// straight to the call, never store it.")?;
        writeln!(f, "    #[inline]")?;
        writeln!(
            f,
            "    pub(crate) fn to_sys(self) -> flowi_sys::{} {{",
            sdef.name
        )?;
        // Only a direct string field reaches the fl_frame_str extern; a nested twin
        // lowers through its own to_sys, which carries its own block. An
        // unconditional wrapper would leave an unused_unsafe on every string-free
        // config.
        let copies_strings = sdef
            .variables
            .iter()
            .any(|var| var.vtype == VariableType::Str);
        let (open, close, indent) = if copies_strings {
            writeln!(
                f,
                "        // SAFETY: fl_frame_str copies len bytes from the pointer before returning, so each"
            )?;
            writeln!(
                f,
                "        // borrowed field only has to outlive this call. It asserts an active frame - every"
            )?;
            writeln!(f, "        // caller is a façade slot emitting inside one.")?;
            ("        unsafe {\n", "        }\n", "    ")
        } else {
            ("", "", "")
        };
        write!(f, "{}", open)?;
        writeln!(f, "        {}flowi_sys::{} {{", indent, sdef.name)?;
        for var in &sdef.variables {
            writeln!(
                f,
                "            {}{}: {},",
                indent,
                Self::rust_ident(&var.name),
                Self::mirror_field_to_sys(var)
            )?;
        }
        writeln!(f, "        {}}}", indent)?;
        write!(f, "{}", close)?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)
    }

    /// Emit one façade method for a slot, forwarding to the direct `fl_*` function.
    fn generate_facade_fn<W: Write>(f: &mut W, func: &Function) -> io::Result<()> {
        if func.is_status {
            return Self::generate_facade_status_fn(f, func);
        }
        if func.is_transfer {
            return Self::generate_facade_transfer_fn(f, func);
        }
        if Self::is_option_shape(func) {
            return Self::generate_facade_option_fn(f, func);
        }
        let method = Self::facade_method_name(&func.name);
        let (params, ffi, prelude) = Self::facade_args(func, None, None);
        let params = params.join(", ");
        let ffi = ffi.join(", ");
        // The public method drops any _impl suffix; the C function keeps its full
        // c_name.
        let call = format!("flowi_sys::{}({})", func.c_name, ffi);
        let (ret_ty, tail) = Self::facade_call_expr(func, call);

        Self::write_comment(f, &func.doc_comments, 4)?;
        // The primary slot's method is new but returns the widget's Signal, not
        // Self - a deliberate immediate-mode trade-off, so clippy's
        // constructor-convention lint is silenced on exactly that method.
        if method == "new" {
            writeln!(f, "    #[allow(clippy::new_ret_no_self)]")?;
        }
        Self::write_facade_method(f, method, &params, ret_ty.as_deref(), |f| {
            Self::write_unsafe_body(f, &prelude, &tail)
        })
    }

    fn generate_facade_option_fn<W: Write>(f: &mut W, func: &Function) -> io::Result<()> {
        let LoweredResult::Option { ty } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!("option emitter called for non-option slot")
        };
        let out_idx = Self::out_param_index(func).expect("option shape has out param");
        let (params, ffi, prelude) = Self::facade_args(func, None, Some(out_idx));
        let call = format!("flowi_sys::{}({})", func.c_name, ffi.join(", "));
        let method = Self::facade_method_name(&func.name);
        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(
            f,
            method,
            &params.join(", "),
            Some(&format!("Option<{}>", ty)),
            |f| {
                writeln!(
                    f,
                    "        let mut out = core::mem::MaybeUninit::<{}>::uninit();",
                    ty
                )?;
                writeln!(f, "        let present = unsafe {{")?;
                for line in &prelude {
                    writeln!(f, "            {}", line)?;
                }
                writeln!(f, "            {}", call)?;
                writeln!(f, "        }};")?;
                write!(f, "{}", safety_assume_init("        ", "true"))?;
                writeln!(f, "        present.then(|| unsafe {{ out.assume_init() }})")
            },
        )
    }

    fn generate_facade_transfer_fn<W: Write>(f: &mut W, func: &Function) -> io::Result<()> {
        let LoweredResult::Transfer { owned_ty } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!("transfer emitter called for non-transfer slot")
        };
        let (params, ffi, prelude) = Self::facade_args(func, None, None);
        let call = format!("flowi_sys::{}({})", func.c_name, ffi.join(", "));
        let method = Self::facade_method_name(&func.name);
        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(f, method, &params.join(", "), Some(&owned_ty), |f| {
            writeln!(f, "        unsafe {{")?;
            for line in &prelude {
                writeln!(f, "            {}", line)?;
            }
            writeln!(f, "            let ptr = {};", call)?;
            writeln!(f, "            {} {{ ptr }}", owned_ty)?;
            writeln!(f, "        }}")
        })
    }

    /// Emit a `[status]` façade method: `pub fn <m>(...) -> Result<T, crate::FlError>`,
    /// the trailing `*mut T` out-param becoming the Ok value (or () when the slot
    /// is status-only). Forwards to the direct `flowi_sys::<c_name>` function and
    /// decodes the returned status code through crate::FlError::from_status.
    fn generate_facade_status_fn<W: Write>(f: &mut W, func: &Function) -> io::Result<()> {
        let LoweredResult::Status { ok_ty, has_out } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!("status emitter called for non-status slot")
        };
        let method = Self::facade_method_name(&func.name);
        let out_idx = Self::out_param_index(func);
        let (params, ffi, prelude) = Self::facade_args(func, None, out_idx);
        let params = params.join(", ");
        let ffi = ffi.join(", ");
        let call = format!("flowi_sys::{}({})", func.c_name, ffi);
        let ret_ty = format!("Result<{}, crate::FlError>", ok_ty);

        Self::write_comment(f, &func.doc_comments, 4)?;
        // The slot call (and any `[retained]` prelude) share one unsafe block, then
        // the status decode and Ok-lift stay in safe code so ? reads cleanly.
        Self::write_facade_method(f, method, &params, Some(&ret_ty), |f| {
            if has_out {
                writeln!(
                    f,
                    "        let mut out = core::mem::MaybeUninit::<{}>::uninit();",
                    ok_ty
                )?;
            }
            writeln!(f, "        let status = unsafe {{")?;
            for line in &prelude {
                writeln!(f, "            {}", line)?;
            }
            writeln!(f, "            {}", call)?;
            writeln!(f, "        }};")?;
            writeln!(
                f,
                "        crate::FlError::from_status({})?;",
                Self::status_as_i32(LooseSymbolSurface::DirectLink, func)
            )?;
            if has_out {
                write!(f, "{}", safety_assume_init("        ", "a success status"))?;
                writeln!(f, "        Ok(unsafe {{ out.assume_init() }})")
            } else {
                writeln!(f, "        Ok(())")
            }
        })
    }

    /// Write a method body's unsafe block: the one-line `unsafe { <tail> }`
    /// when there is no prelude, or a multi-line block running the `[retained]`
    /// copy statements before the slot call.
    fn write_unsafe_body<W: Write>(f: &mut W, prelude: &[String], tail: &str) -> io::Result<()> {
        if prelude.is_empty() {
            return writeln!(f, "        unsafe {{ {} }}", tail);
        }
        writeln!(f, "        unsafe {{")?;
        for line in prelude {
            writeln!(f, "            {}", line)?;
        }
        writeln!(f, "            {}", tail)?;
        writeln!(f, "        }}")?;
        Ok(())
    }

    // ---- RAII opaque-handle façade ---------------------------------------
    //
    // An `api <Domain>` block with a `[drop]` slot is an RAII opaque-handle domain:
    // the C side hands out a handle the app owns and frees (a bare `void*`, or a
    // typed opaque pointer like `*App`), and the ergonomic Rust binding is a
    // handle-owning struct that frees it on Drop. The emitter synthesizes the
    // struct + Drop + the receiver methods; the constructor and any convenience
    // slots stay `[manual]`, hand-written on this same generated type.

    /// The `[drop]` slot of an api block, if any - its presence marks the block
    /// an RAII opaque-handle façade.
    fn api_drop_fn(api: &Api) -> Option<&Function> {
        api.functions.iter().find(|func| func.is_drop)
    }

    /// The sole pointer argument of an RAII block's `[drop]` destructor - the handle
    /// it owns, a bare `*void` or a typed opaque pointer (`*App`).
    fn raii_handle_arg(drop_fn: &Function) -> Option<&Variable> {
        drop_fn.function_args.iter().find(|a| a.pointer)
    }

    /// The handle parameter name an RAII block threads through its receiver slots:
    /// the name of the `[drop]` destructor's handle arg (state / set / app).
    /// Every other slot that takes an argument of this name receives it as
    /// self.handle; a slot without it (the constructor) is left hand-written.
    fn raii_handle_name(drop_fn: &Function) -> &str {
        Self::raii_handle_arg(drop_fn)
            .map(|a| a.name.as_str())
            .unwrap_or("handle")
    }

    /// The Rust spelling of the owned handle field - `*mut` of the `[drop]` arg's
    /// type. A typed opaque handle becomes `*mut flowi_sys::<T>`, so Drop and the
    /// receiver slots thread it straight into the `fl_*` slots that take that exact
    /// pointer - no cast.
    fn raii_handle_type(drop_fn: &Function) -> String {
        Self::raii_handle_arg(drop_fn)
            .map(|a| format!("*mut {}", Self::facade_base_type(a)))
            .unwrap_or_else(|| "*mut core::ffi::c_void".to_owned())
    }

    /// Whether an RAII slot gets a generated receiver method: not the `[drop]`
    /// destructor (emitted as Drop), not `[manual]` (hand-written), not varargs.
    /// The caller additionally requires a receiver argument (else it is the
    /// constructor, which stays hand-written).
    fn raii_generates(func: &Function) -> bool {
        !func.is_drop
            && func.func_type != FunctionType::Manual
            && !func.has_varargs
            && !func.is_c_only
            && !Self::has_extern_opaque_arg(func)
    }

    /// Emit one RAII receiver method, forwarding to the direct `fl_*` function with
    /// the handle argument supplied from self.handle. The receiver is &self for a
    /// `[const]` slot, else &mut self; the emitted name honors `[rename(...)]`.
    fn generate_raii_method<W: Write>(f: &mut W, func: &Function, handle: &str) -> io::Result<()> {
        let method = func.rename.as_deref().unwrap_or(&func.name);
        let receiver = if func.is_const { "&self" } else { "&mut self" };

        if func.is_status {
            return Self::generate_raii_status_method(f, func, handle, receiver, method);
        }
        if Self::is_option_shape(func)
            && func
                .function_args
                .last()
                .is_some_and(|arg| arg.name != handle)
        {
            return Self::generate_raii_option_method(f, func, handle, receiver, method);
        }
        if func.is_transfer {
            return Self::generate_raii_transfer_method(f, func, handle, receiver, method);
        }

        let (arg_params, ffi, prelude) = Self::facade_args(func, Some(handle), None);
        let mut params = vec![receiver.to_owned()];
        params.extend(arg_params);
        let params = params.join(", ");
        let ffi = ffi.join(", ");
        let call = format!("flowi_sys::{}({})", func.c_name, ffi);
        let (ret_ty, tail) = if Self::is_option_shape(func)
            && func
                .function_args
                .last()
                .is_some_and(|arg| arg.name == handle)
        {
            (Some("bool".to_owned()), call)
        } else {
            Self::facade_call_expr(func, call)
        };

        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(f, method, &params, ret_ty.as_deref(), |f| {
            Self::write_unsafe_body(f, &prelude, &tail)
        })
    }

    fn generate_raii_status_method<W: Write>(
        f: &mut W,
        func: &Function,
        handle: &str,
        receiver: &str,
        method: &str,
    ) -> io::Result<()> {
        let LoweredResult::Status { ok_ty, has_out } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!()
        };
        let out_idx = Self::out_param_index(func);
        let (mut params, ffi, prelude) = Self::facade_args(func, Some(handle), out_idx);
        params.insert(0, receiver.to_owned());
        let call = format!("flowi_sys::{}({})", func.c_name, ffi.join(", "));
        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(
            f,
            method,
            &params.join(", "),
            Some(&format!("Result<{}, crate::FlError>", ok_ty)),
            |f| {
                if has_out {
                    writeln!(
                        f,
                        "        let mut out = core::mem::MaybeUninit::<{}>::uninit();",
                        ok_ty
                    )?;
                }
                writeln!(f, "        let status = unsafe {{")?;
                for line in &prelude {
                    writeln!(f, "            {}", line)?;
                }
                writeln!(f, "            {}", call)?;
                writeln!(f, "        }};")?;
                writeln!(
                    f,
                    "        crate::FlError::from_status({})?;",
                    Self::status_as_i32(LooseSymbolSurface::DirectLink, func)
                )?;
                if has_out {
                    write!(f, "{}", safety_assume_init("        ", "a success status"))?;
                    writeln!(f, "        Ok(unsafe {{ out.assume_init() }})")
                } else {
                    writeln!(f, "        Ok(())")
                }
            },
        )
    }

    fn generate_raii_option_method<W: Write>(
        f: &mut W,
        func: &Function,
        handle: &str,
        receiver: &str,
        method: &str,
    ) -> io::Result<()> {
        let LoweredResult::Option { ty } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!()
        };
        let out_idx = Self::out_param_index(func).expect("option shape has out param");
        let (mut params, ffi, prelude) = Self::facade_args(func, Some(handle), Some(out_idx));
        params.insert(0, receiver.to_owned());
        let call = format!("flowi_sys::{}({})", func.c_name, ffi.join(", "));
        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(
            f,
            method,
            &params.join(", "),
            Some(&format!("Option<{}>", ty)),
            |f| {
                writeln!(
                    f,
                    "        let mut out = core::mem::MaybeUninit::<{}>::uninit();",
                    ty
                )?;
                writeln!(f, "        let present = unsafe {{")?;
                for line in &prelude {
                    writeln!(f, "            {}", line)?;
                }
                writeln!(f, "            {}", call)?;
                writeln!(f, "        }};")?;
                write!(f, "{}", safety_assume_init("        ", "true"))?;
                writeln!(f, "        present.then(|| unsafe {{ out.assume_init() }})")
            },
        )
    }

    fn generate_raii_transfer_method<W: Write>(
        f: &mut W,
        func: &Function,
        handle: &str,
        receiver: &str,
        method: &str,
    ) -> io::Result<()> {
        let LoweredResult::Transfer { owned_ty } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::DirectLink, func)
                .unwrap_or_else(|diag| panic!("{}", diag))
        else {
            unreachable!()
        };
        let (mut params, ffi, prelude) = Self::facade_args(func, Some(handle), None);
        params.insert(0, receiver.to_owned());
        let call = format!("flowi_sys::{}({})", func.c_name, ffi.join(", "));
        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(f, method, &params.join(", "), Some(&owned_ty), |f| {
            writeln!(f, "        unsafe {{")?;
            for line in &prelude {
                writeln!(f, "            {}", line)?;
            }
            writeln!(f, "            let ptr = {};", call)?;
            writeln!(f, "            {} {{ ptr }}", owned_ty)?;
            writeln!(f, "        }}")
        })
    }

    /// Emit one RAII opaque-handle block: the handle-owning struct, its Drop
    /// (calling the `[drop]` destructor and nulling the handle), and the generated
    /// receiver methods. The handle field is pub(crate) so the flowi crate's
    /// hand-written constructor / bespoke slots (and List) can reach it.
    fn generate_raii_facade<W: Write>(f: &mut W, api: &Api, drop_fn: &Function) -> io::Result<()> {
        let handle = Self::raii_handle_name(drop_fn);
        let handle_ty = Self::raii_handle_type(drop_fn);
        let transfer_destroy: std::collections::HashSet<&str> = api
            .functions
            .iter()
            .filter_map(|func| func.transfer_free.as_deref())
            .collect();

        Self::write_comment(f, &api.doc_comments, 0)?;
        writeln!(f, "pub struct {} {{", api.name)?;
        writeln!(f, "    pub(crate) handle: {},", handle_ty)?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        writeln!(f, "impl Drop for {} {{", api.name)?;
        writeln!(f, "    fn drop(&mut self) {{")?;
        writeln!(f, "        if !self.handle.is_null() {{")?;
        writeln!(
            f,
            "            unsafe {{ flowi_sys::{}(self.handle) }};",
            drop_fn.c_name
        )?;
        writeln!(f, "            self.handle = core::ptr::null_mut();")?;
        writeln!(f, "        }}")?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        let mut methods = api
            .functions
            .iter()
            .filter(|func| {
                Self::raii_generates(func)
                    && !transfer_destroy.contains(func.name.as_str())
                    && func.function_args.iter().any(|a| a.name == handle)
            })
            .peekable();
        if methods.peek().is_some() {
            writeln!(f, "impl {} {{", api.name)?;
            let mut first = true;
            for func in methods {
                if !first {
                    writeln!(f)?;
                }
                first = false;
                Self::generate_raii_method(f, func, handle)?;
            }
            writeln!(f, "}}")?;
            writeln!(f)?;
        }
        Ok(())
    }

    // ---- Scope-guard façade ----------------------------------------------
    //
    // An `api <Domain>` block with a `[scope_begin]` / `[scope_end]` pair models a
    // thread-local begin/end scope (fl_popup_begin / fl_popup_end): there is no
    // owned handle - the scope is state on the global UI context - so the ergonomic
    // binding is a zero-sized `<Domain>Scope` guard returned by the begin method,
    // whose Drop runs the paired end slot. The end slot is emitted as an explicit
    // close that consumes the guard by value (and mem::forgets it), so a double
    // close is a compile error rather than a runtime double end.

    /// The `[scope_begin]` slot of an api block, if any.
    fn api_scope_begin_fn(api: &Api) -> Option<&Function> {
        api.functions.iter().find(|func| func.is_scope_begin)
    }

    /// The `[scope_end]` slot of an api block, if any.
    fn api_scope_end_fn(api: &Api) -> Option<&Function> {
        api.functions.iter().find(|func| func.is_scope_end)
    }

    /// The generated guard type name for a scope-guard domain: `<Domain>Scope`
    /// (e.g. Popup → PopupScope).
    fn scope_guard_name(api: &Api) -> String {
        format!("{}Scope", api.name)
    }

    /// Emit the `<Domain>Scope` guard for a scope-guard domain: a zero-sized
    /// `#[must_use]` token struct + an impl Drop running the paired `[scope_end]`
    /// slot. The end slot threads no arguments - the scope is thread-local state,
    /// not an owned handle.
    fn generate_scope_guard<W: Write>(
        f: &mut W,
        api: &Api,
        begin_fn: &Function,
        end_fn: &Function,
    ) -> io::Result<()> {
        let guard = Self::scope_guard_name(api);
        let begin = Self::facade_method_name(&begin_fn.name);
        let end = Self::facade_method_name(&end_fn.name);

        writeln!(
            f,
            "/// RAII scope guard returned by [`{api}::{begin}`]. The scope it opens closes when this guard drops",
            api = api.name,
            begin = begin
        )?;
        writeln!(
            f,
            "/// (the paired {end_c} runs); bind it (let _guard = {api}::{begin}(...)) so it lives for the duration",
            end_c = end_fn.c_name,
            api = api.name,
            begin = begin
        )?;
        writeln!(
            f,
            "/// of the scoped content rather than closing immediately. Close it explicitly instead by handing it"
        )?;
        writeln!(
            f,
            "/// to [`{api}::{end}`], which consumes the guard so the scope never closes twice.",
            api = api.name,
            end = end
        )?;
        writeln!(
            f,
            "#[must_use = \"the scope closes when this guard drops; bind it for the duration of the scoped content\"]"
        )?;
        writeln!(f, "pub struct {} {{", guard)?;
        writeln!(
            f,
            "    // Zero-sized token: the scope is state on the thread-local UI context, so the guard carries no",
        )?;
        writeln!(
            f,
            "    // data - its sole job is to run {end} on drop. Private so the only way to obtain one is",
            end = end_fn.c_name
        )?;
        writeln!(f, "    // {api}::{begin}.", api = api.name, begin = begin)?;
        writeln!(f, "    _priv: (),")?;
        writeln!(f, "}}")?;
        writeln!(f)?;

        writeln!(f, "impl Drop for {} {{", guard)?;
        writeln!(f, "    fn drop(&mut self) {{")?;
        writeln!(f, "        unsafe {{ flowi_sys::{}() }};", end_fn.c_name)?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;
        Ok(())
    }

    /// Emit the `[scope_begin]` slot as a guard-returning method: forward to the
    /// direct `fl_*` begin function (which returns void), then hand back a
    /// `<Domain>Scope` token.
    fn generate_scope_begin_fn<W: Write>(
        f: &mut W,
        func: &Function,
        guard: &str,
    ) -> io::Result<()> {
        let method = Self::facade_method_name(&func.name);
        let (params, ffi, prelude) = Self::facade_args(func, None, None);
        assert!(
            prelude.is_empty(),
            "[retained] is only supported on stateless façade slots ({})",
            func.name
        );
        let params = params.join(", ");
        let ffi = ffi.join(", ");
        let call = format!("flowi_sys::{}({})", func.c_name, ffi);

        Self::write_comment(f, &func.doc_comments, 4)?;
        Self::write_facade_method(f, method, &params, Some(guard), |f| {
            writeln!(f, "        unsafe {{ {} }};", call)?;
            writeln!(f, "        {} {{ _priv: () }}", guard)
        })
    }

    /// Emit the `[scope_end]` slot as a guard-consuming method: take the
    /// `<Domain>Scope` token by value and mem::forget it so its Drop does not also
    /// run the end slot, then run the paired end forward exactly once. The end slot
    /// threads no arguments; the scope is thread-local state.
    fn generate_scope_end_fn<W: Write>(f: &mut W, func: &Function, guard: &str) -> io::Result<()> {
        let method = Self::facade_method_name(&func.name);

        Self::write_comment(f, &func.doc_comments, 4)?;
        writeln!(f, "    #[inline]")?;
        writeln!(f, "    pub fn {}(scope: {}) {{", method, guard)?;
        writeln!(
            f,
            "        // Consume the guard without running its Drop, then close once: an explicit"
        )?;
        writeln!(
            f,
            "        // {method} plus the guard's drop (or two {method} calls) is a compile error, not a"
        )?;
        writeln!(f, "        // runtime double close.")?;
        writeln!(f, "        core::mem::forget(scope);")?;
        writeln!(f, "        unsafe {{ flowi_sys::{}() }}", func.c_name)?;
        writeln!(f, "    }}")?;
        Ok(())
    }

    /// Emit the ergonomic façade module for one def: per api block, either an
    /// RAII opaque-handle struct (a `[drop]` slot is present) or a `pub struct
    /// <Domain>;` + `impl <Domain>` of free-function forwarders (with a
    /// `<Domain>Scope` guard prepended when the block carries a `[scope_begin]` /
    /// `[scope_end]` pair). Returns true if anything was written (so the mod index
    /// can list it).
    pub fn generate_facade(
        fl_ui_gen_dir: &str,
        api_def: &ApiDef,
        script: &str,
    ) -> io::Result<bool> {
        // A `#[attributes(service)]` block has no direct-link façade: the
        // external-consumer wrapper pass owns that surface.
        let mirrors: Vec<&Struct> = api_def.structs.iter().filter(|s| s.is_mirror()).collect();
        let any = !mirrors.is_empty()
            || api_def
                .apis
                .iter()
                .filter(|api| !api.is_service)
                .any(|api| {
                    Self::api_drop_fn(api).is_some()
                        || api.functions.iter().any(Self::facade_generates)
                });
        if !any {
            return Ok(false);
        }

        // The body is buffered so the file header can state the shared safety
        // argument only for defs that actually forward through unsafe.
        let mut body: Vec<u8> = Vec::new();
        let f = &mut body;

        // The safe config twins first: a slot in this same def may take one, and a
        // def can consist of nothing else (the shared widget config).
        for sdef in mirrors {
            Self::generate_mirror_struct(f, sdef)?;
        }

        for api in &api_def.apis {
            if api.is_service {
                continue;
            }
            let destroy: std::collections::HashSet<&str> = api
                .functions
                .iter()
                .filter_map(|func| func.transfer_free.as_deref())
                .collect();
            let transfer_pairs = Self::validate_transfer_api(api)
                .unwrap_or_else(|diag| panic!("api_gen: façade `{}`: {}", api.name, diag));
            let mut seen_owned = std::collections::HashSet::new();
            for (_, ret, free_fn) in transfer_pairs {
                if seen_owned.insert(ret.type_name.clone()) {
                    let mut owned = String::new();
                    Self::write_owned_newtype(
                        &mut owned,
                        LooseSymbolSurface::DirectLink,
                        Some("flowi_sys"),
                        &api.name,
                        ret,
                        &free_fn.c_name,
                        &Self::loose_symbol_ffi_type(
                            LooseSymbolSurface::DirectLink,
                            &free_fn.function_args[0],
                        ),
                    );
                    write!(f, "{}", owned)?;
                }
            }
            if let Some(drop_fn) = Self::api_drop_fn(api) {
                Self::generate_raii_facade(f, api, drop_fn)?;
                continue;
            }
            if !api.functions.iter().any(Self::facade_generates) {
                continue;
            }
            // A `[scope_begin]` / `[scope_end]` pair prepends a `<Domain>Scope` guard
            // before the stateless façade struct; the begin slot then emits as a
            // guard-returning method instead of a bare void forwarder.
            let scope = Self::api_scope_begin_fn(api).zip(Self::api_scope_end_fn(api));
            if let Some((begin_fn, end_fn)) = scope {
                Self::generate_scope_guard(f, api, begin_fn, end_fn)?;
            }

            Self::write_comment(f, &api.doc_comments, 0)?;
            writeln!(f, "pub struct {};", api.name)?;
            writeln!(f)?;
            writeln!(f, "impl {} {{", api.name)?;
            let mut first = true;
            for func in api.functions.iter().filter(|func| {
                Self::facade_generates(func) && !destroy.contains(func.name.as_str())
            }) {
                if !first {
                    writeln!(f)?;
                }
                first = false;
                if scope.is_some() && func.is_scope_begin {
                    Self::generate_scope_begin_fn(f, func, &Self::scope_guard_name(api))?;
                } else if scope.is_some() && func.is_scope_end {
                    Self::generate_scope_end_fn(f, func, &Self::scope_guard_name(api))?;
                } else {
                    Self::generate_facade_fn(f, func)?;
                }
            }
            writeln!(f, "}}")?;
            writeln!(f)?;
        }

        let body = String::from_utf8(body).expect("api_gen: façade output is UTF-8");
        let filename = format!("{}/{}.rs", fl_ui_gen_dir, api_def.base_filename);
        let mut out = BufWriter::new(File::create(&filename)?);
        write!(out, "{}{}", Self::generated_header(&body, script), body)?;
        Ok(true)
    }

    /// The tree-wide dead-code allow a full-API sys mirror opts into
    /// (Config::rust_allow_dead_code); a 1:1 consumer tree omits it so orphaned
    /// bindings warn.
    fn write_mirror_allow<W: Write>(f: &mut W, allow_dead_code: bool) -> io::Result<()> {
        if allow_dead_code {
            writeln!(
                f,
                "// These bindings mirror the full C API surface; not every item is\n\
                 // consumed from Rust, so the unused ones are expected, not a defect."
            )?;
            writeln!(f, "#![allow(dead_code)]")?;
            writeln!(f)?;
        }
        Ok(())
    }

    /// Generate the flowi façade generated/mod.rs index. One pub mod per def
    /// that produced a façade, in the given (already filename-sorted) order.
    pub fn generate_facade_mod_file(
        fl_ui_gen_dir: &str,
        modules: &[String],
        allow_dead_code: bool,
        script: &str,
    ) -> io::Result<()> {
        let filename = format!("{}/mod.rs", fl_ui_gen_dir);
        let mut f = BufWriter::new(File::create(&filename)?);
        write!(f, "{}", crate::emit_util::header(script))?;
        writeln!(f)?;
        Self::write_mirror_allow(&mut f, allow_dead_code)?;
        for m in modules {
            writeln!(f, "pub mod {};", m)?;
        }
        Ok(())
    }

    /// Generate the generated/mod.rs submodule index. One pub mod per def,
    /// sorted by filename for a deterministic, no-op-on-regen diff.
    ///
    /// The consume-side reader modules are declared here too, and are the one
    /// thing in the tree whose visibility is conditional: crate-private in a real
    /// plugin build, public under read_feature so the tests that drive a reader
    /// without an FFI call can reach it from another crate.
    pub fn generate_mod_file(
        rust_dir: &str,
        api_defs: &[&ApiDef],
        allow_dead_code: bool,
        read_modules: &[String],
        read_feature: Option<&str>,
        script: &str,
    ) -> io::Result<()> {
        let filename = format!("{}/mod.rs", rust_dir);
        let mut f = BufWriter::new(File::create(&filename)?);

        write!(f, "{}", crate::emit_util::header(script))?;
        writeln!(f)?;
        Self::write_mirror_allow(&mut f, allow_dead_code)?;
        for api_def in api_defs {
            writeln!(f, "pub mod {};", api_def.base_filename)?;
        }
        if !read_modules.is_empty() {
            let feature = read_feature.expect("api_gen: reader modules want --read-test-feature");
            for module in read_modules {
                writeln!(f)?;
                writeln!(f, "#[cfg(not(feature = \"{}\"))]", feature)?;
                writeln!(f, "pub(crate) mod {};", module)?;
                writeln!(f, "#[cfg(feature = \"{}\")]", feature)?;
                writeln!(f, "pub mod {};", module)?;
            }
        }
        Ok(())
    }

    // ===================================================================
    // Service-consume wrapper
    //
    // A `#[attributes(service)]` `api <Domain>` block is a foundation service flowi
    // exports as plain C symbols: each slot's name is the exported symbol
    // (probe_parse), so an external consumer linking the shared library calls it
    // directly. This backend emits the consume side: per service def, one wrapper
    // module holding an extern "C" block declaring the exported symbols (spelled
    // prefix-free, so the Rust output is identical under any --naming profile) and
    // `<Domain>`, a safe wrapper forwarding each non-`[manual]` slot to its symbol.
    //
    // Any slot the ownership-annotation rules cannot classify (an unannotated
    // raw-pointer return, a raw void pointer param) is a hard-fail with a
    // diagnostic - never a guess.

    /// Base FFI spelling of a value's type, no pointer qualifier.
    fn loose_symbol_ffi_base(surface: LooseSymbolSurface, var: &Variable) -> String {
        Self::loose_symbol_base_type(surface, var)
    }

    /// Full FFI spelling of a value (base + pointer / fixed-array qualifier) - the
    /// type an exported service symbol's extern "C" declaration crosses.
    fn loose_symbol_ffi_type(surface: LooseSymbolSurface, var: &Variable) -> String {
        let base = Self::apply_pointer(var, Self::loose_symbol_ffi_base(surface, var));
        match &var.array {
            Some(ArrayType::SizedArray(n)) => format!("[{}; {}]", base, n),
            _ => base,
        }
    }

    /// Signature fragment (params, `-> ret`) for an exported service symbol's
    /// extern "C" declaration, spelled in the surface's FFI types. An unsized array
    /// arg lowers to a `ptr, <name>_size: u32` pair.
    fn loose_symbol_sig_parts(
        surface: LooseSymbolSurface,
        args: &[Variable],
        ret: Option<&Variable>,
    ) -> (String, String) {
        let params = args
            .iter()
            .filter(|a| a.vtype != VariableType::SelfType)
            .map(|a| {
                let name = Self::rust_ident(&a.name);
                if matches!(a.array, Some(ArrayType::Unsized)) {
                    let base = Self::loose_symbol_ffi_base(surface, a);
                    let ptr = if a.pointer {
                        format!("*mut {}", base)
                    } else {
                        format!("*const {}", base)
                    };
                    format!("{}: {}, {}_size: u32", name, ptr, name)
                } else {
                    format!("{}: {}", name, Self::loose_symbol_ffi_type(surface, a))
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let ret = match ret {
            Some(v) => format!(" -> {}", Self::loose_symbol_ffi_type(surface, v)),
            None => String::new(),
        };
        (params, ret)
    }

    /// Owning-newtype name for a `[transfer]` return of `*<Pointee>` (Widget ->
    /// OwnedWidget).
    fn owned_newtype_name(pointee: &str) -> String {
        format!("Owned{}", pointee)
    }

    fn validate_transfer_api(api: &Api) -> Result<Vec<(&Function, &Variable, &Function)>, String> {
        let destroy: std::collections::HashSet<&str> = api
            .functions
            .iter()
            .filter_map(|func| func.transfer_free.as_deref())
            .collect();
        let mut pointees = std::collections::HashSet::new();
        let mut pairs = Vec::new();
        for func in &api.functions {
            let Some(free_name) = func.transfer_free.as_deref() else {
                continue;
            };
            let ret = func.return_val.as_ref().ok_or_else(|| {
                format!(
                    "slot `{}`: a `[transfer]` return must be a pointer to a named type",
                    func.name
                )
            })?;
            if !(ret.pointer || ret.const_pointer) || ret.type_name == "void" {
                return Err(format!(
                    "slot `{}`: a `[transfer]` return must be a pointer to a named type",
                    func.name
                ));
            }
            if ret.is_extern_opaque {
                return Err(format!(
                    "slot `{}`: cannot transfer ownership of the `extern opaque` type `{}` — mark the slot `[manual]`",
                    func.name, ret.type_name
                ));
            }
            let free_fn = api
                .functions
                .iter()
                .find(|candidate| candidate.name == free_name)
                .ok_or_else(|| {
                    format!(
                        "slot `{}`: `[transfer(free = {})]` names no slot in this service",
                        func.name, free_name
                    )
                })?;
            let valid_free = free_fn.function_args.len() == 1
                && (free_fn.function_args[0].pointer || free_fn.function_args[0].const_pointer)
                && free_fn.function_args[0].type_name == ret.type_name;
            if !valid_free {
                return Err(format!(
                    "slot `{}`: destroy slot `{}` must take exactly one `*{}` parameter to pair with the `[transfer]` return",
                    func.name, free_name, ret.type_name
                ));
            }
            pointees.insert(ret.type_name.clone());
            pairs.push((func, ret, free_fn));
        }
        for func in &api.functions {
            if func.func_type == FunctionType::Manual
                || func.has_varargs
                || destroy.contains(func.name.as_str())
            {
                continue;
            }
            for arg in &func.function_args {
                if arg.is_transfer && !pointees.contains(&arg.type_name) {
                    return Err(format!(
                        "slot `{}`: `[transfer]` parameter `{}` has no owning newtype — no `[transfer(free = ...)]` slot returns `*{}` in this service",
                        func.name, arg.name, arg.type_name
                    ));
                }
            }
        }
        Ok(pairs)
    }

    /// A method's parameter list with the &self receiver prepended.
    fn sig_with_self(params: &[String]) -> String {
        if params.is_empty() {
            "&self".to_owned()
        } else {
            format!("&self, {}", params.join(", "))
        }
    }

    /// The forwarding call for a slot: a direct call to the exported C symbol.
    /// symbol is the slot's raw name (which is its c_name). raw is the module
    /// path the declaration lives at when the consumer generates a raw bindings tree
    /// (crate::generated::probe); None means the wrapper module declared it itself.
    fn slot_call(raw: Option<&str>, symbol: &str, ffi: &[String]) -> String {
        match raw {
            Some(path) => format!("{}::{}({})", path, symbol, ffi.join(", ")),
            None => format!("{}({})", symbol, ffi.join(", ")),
        }
    }

    /// The slots of an api block that get a generated wrapper method: everything
    /// but the hand-written (`[manual]`), the varargs (inexpressible from stable
    /// Rust), and the `[transfer(free = ...)]` destructors (reached only through an
    /// owning newtype's Drop).
    fn service_generated_slots(api: &Api) -> Vec<&Function> {
        let destroy: std::collections::HashSet<&str> = api
            .functions
            .iter()
            .filter_map(|f| f.transfer_free.as_deref())
            .collect();
        api.functions
            .iter()
            .filter(|f| {
                f.func_type != FunctionType::Manual
                    && !f.has_varargs
                    && !f.is_c_only
                    && !destroy.contains(f.name.as_str())
            })
            .collect()
    }

    /// The safe wrapper's method name for a slot: the exported symbol with the
    /// redundant naming prefix stripped, so a consumer reads
    /// Probe::new().parse(..) rather than .probe_parse(..).
    ///
    /// A service slot's name is the exported C symbol, so what it carries ahead of
    /// the verb depends on the profile: flowi's slots bake in only the domain
    /// (probe_parse), a profile whose exports are namespaced bakes in the function
    /// prefix too (rp_metadata_get_waveform_image). Both are peeled, function prefix
    /// first, and either may be absent - a slot carrying neither keeps its own name,
    /// minus any _impl C body-name suffix.
    fn service_method_name(naming: &Naming, api_snake: &str, slot: &str) -> String {
        let func_prefix = format!("{}_", naming.func_prefix);
        let base = slot.strip_prefix(&func_prefix).unwrap_or(slot);
        let domain_prefix = format!("{}_", api_snake);
        let base = base.strip_prefix(&domain_prefix).unwrap_or(base);
        // Peeling the prefixes off a slot can leave a bare Rust keyword
        // (store_try -> try), and a method named one does not parse.
        Self::rust_ident(base.strip_suffix("_impl").unwrap_or(base))
    }

    /// Index of a slot's trailing `*mut T` out-parameter (the `[status]` Ok value
    /// / the Option payload), or None when the last arg is not an out-param.
    fn out_param_index(func: &Function) -> Option<usize> {
        let i = func.function_args.len().checked_sub(1)?;
        let a = &func.function_args[i];
        (a.pointer
            && !a.const_pointer
            && !a.is_transfer
            && a.type_name != "void"
            && a.array.is_none())
        .then_some(i)
    }

    /// Whether a slot maps to `Option<T>`: a bool return plus a trailing `*mut T`
    /// out-param, and no `[status]` (which would make it a Result) / `[transfer]`.
    fn is_option_shape(func: &Function) -> bool {
        !func.is_status
            && !func.is_transfer
            && func
                .return_val
                .as_ref()
                .is_some_and(|r| r.vtype == VariableType::Primitive && r.type_name == "bool")
            && Self::out_param_index(func).is_some()
    }

    /// Lower all of a slot's args into parallel (rust_params, ffi_exprs, prelude)
    /// vectors. out_idx names an out-param handled by the caller (its ffi expr is
    /// out.as_mut_ptr(), contributing no parameter).
    fn service_call_args(func: &Function, out_idx: Option<usize>) -> Result<LoweredArgs, String> {
        Self::lower_loose_symbol_args(LooseSymbolSurface::ExternalConsumer, func, None, out_idx)
    }

    /// Classify an ordinary (non-transfer, non-status, non-option) slot's return as
    /// Some((rust_type, wrap)) - wrap is None for a value passed straight
    /// through - or None for a () return. Hard-fails on a raw-pointer return
    /// (no lifetime source, so no sound safe spelling).
    fn classify_plain_return(func: &Function) -> Result<Option<(String, Option<String>)>, String> {
        match Self::lower_loose_symbol_result(LooseSymbolSurface::ExternalConsumer, func)? {
            LoweredResult::Unit => Ok(None),
            LoweredResult::Value { ty, wrap } => Ok(Some((ty, wrap))),
            other => Err(format!(
                "slot `{}` reached plain return emission with {:?}",
                func.name, other
            )),
        }
    }

    /// Append doc comments to a String at the given indent (the String analogue
    /// of [`write_comment`]).
    fn push_doc(out: &mut String, comments: &[String], indent: usize) {
        let pad = " ".repeat(indent);
        for c in comments {
            if c.is_empty() {
                out.push_str(&format!("{}///\n", pad));
            } else {
                out.push_str(&format!("{}/// {}\n", pad, c));
            }
        }
    }

    /// Emit one wrapper method for a slot, dispatching on its return classification.
    /// api_snake is the service name in snake_case, stripped from the method name.
    fn write_service_method(
        out: &mut String,
        naming: &Naming,
        raw: Option<&str>,
        api_snake: &str,
        func: &Function,
        reads: Option<&ServiceReads>,
    ) -> Result<(), String> {
        Self::push_doc(out, &func.doc_comments, 4);
        let method = Self::service_method_name(naming, api_snake, &func.name);
        let slot = Self::rust_ident(&func.c_name);
        if let Some(record) = reads.and_then(|reads| Self::read_delegating_record(func, reads)) {
            Self::write_read_method(out, raw, func, &method, &slot, &record)
        } else if func.function_args.iter().any(|a| a.opaque_view.is_some()) {
            // Only write_read_method declares the 'a the opaque-param lowering
            // spells, and it is the borrow the reference exists to anchor.
            Err(format!(
                "slot `{}`: takes a `#[view(...)]` `extern opaque` but answers nothing borrowed \
                 from it, so its safe reference anchors no lifetime — mark the slot `[manual]`",
                func.name
            ))
        } else if func.is_transfer {
            Self::write_transfer_method(out, raw, func, &method, &slot)
        } else if func.is_status {
            Self::write_status_method(out, raw, func, &method, &slot)
        } else if Self::is_option_shape(func) {
            Self::write_option_method(out, raw, func, &method, &slot)
        } else {
            Self::write_plain_method(out, raw, func, &method, &slot)
        }
    }

    /// The record a slot answers through a generated reader: a `#[read]` record
    /// borrowing from the arena the slot was handed. That borrow is the only thing the
    /// arena's 'a anchors, and this emitter is the only one that declares it.
    fn read_delegating_record(func: &Function, reads: &ServiceReads) -> Option<ReadRecord> {
        if !func.function_args.iter().any(|a| a.opaque_view.is_some()) {
            return None;
        }
        let ret = func.return_val.as_ref()?;
        let paired = reads.model.structs.get(&ret.type_name)?;
        if !paired.read_root || !read_gen::borrows(reads.model, &ret.type_name) {
            return None;
        }
        Some(ReadRecord {
            owned: format!("{}<'a>", paired.owned.as_ref()?),
            reader: format!(
                "{}::{}_read::{}",
                reads.path,
                paired.def,
                crate::emit_util::read_fn(&paired.name)
            ),
            optional: paired.found_synthesis,
        })
    }

    /// A slot answering a read record: the raw call, then the generated reader over
    /// what it answered, so the crossing's two halves both come from the def.
    fn write_read_method(
        out: &mut String,
        raw: Option<&str>,
        func: &Function,
        method: &str,
        slot: &str,
        record: &ReadRecord,
    ) -> Result<(), String> {
        let LoweredArgs {
            params,
            ffi,
            prelude,
        } = Self::service_call_args(func, None)?;
        let answer = if record.optional {
            format!("Option<{}>", record.owned)
        } else {
            record.owned.clone()
        };
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn {}<'a>({}) -> {} {{\n",
            method,
            Self::sig_with_self(&params),
            answer
        ));
        for line in &prelude {
            out.push_str(&format!("        {}\n", line));
        }
        out.push_str("        unsafe {\n");
        out.push_str(&format!(
            "            let raw = {};\n",
            Self::slot_call(raw, slot, &ffi)
        ));
        out.push_str(&format!("            {}(&raw)\n", record.reader));
        out.push_str("        }\n");
        out.push_str("    }\n");
        Ok(())
    }

    /// An ordinary forwarding method: value/borrow args in, value/()/owned-String
    /// out.
    fn write_plain_method(
        out: &mut String,
        raw: Option<&str>,
        func: &Function,
        method: &str,
        slot: &str,
    ) -> Result<(), String> {
        let LoweredArgs {
            params,
            ffi,
            prelude,
        } = Self::service_call_args(func, None)?;
        let cls = Self::classify_plain_return(func)?;
        out.push_str("    #[inline]\n");
        match &cls {
            None => out.push_str(&format!(
                "    pub fn {}({}) {{\n",
                method,
                Self::sig_with_self(&params)
            )),
            Some((ty, _)) => out.push_str(&format!(
                "    pub fn {}({}) -> {} {{\n",
                method,
                Self::sig_with_self(&params),
                ty
            )),
        }
        for line in &prelude {
            out.push_str(&format!("        {}\n", line));
        }
        let call = Self::slot_call(raw, slot, &ffi);
        let inner = match &cls {
            Some((_, Some(wrap))) => format!("let ret = {}; {}", call, wrap),
            _ => call,
        };
        if Self::has_borrowed_str_return(func) {
            out.push_str(
                "        // SAFETY: a `[borrowed]` return points at host-owned bytes the def\n        // pins live for at least this &self borrow.\n",
            );
        }
        out.push_str(&format!("        unsafe {{ {} }}\n", inner));
        out.push_str("    }\n");
        Ok(())
    }

    /// Whether the slot returns a `[borrowed]` String - the one plain return whose
    /// unsafe block carries an invariant beyond the generic module header, so the
    /// site documents it.
    fn has_borrowed_str_return(func: &Function) -> bool {
        func.is_borrowed
            && func
                .return_val
                .as_ref()
                .is_some_and(|r| r.vtype == VariableType::Str)
    }

    /// The status-to-i32 conversion a `[status]` slot's error check needs. FlError
    /// reads an i32, but the C status is whatever the slot declares, so the cast is
    /// emitted only when the declared type is not already i32 - casting i32 to i32
    /// is a clippy warning in the generated file.
    fn status_as_i32(surface: LooseSymbolSurface, func: &Function) -> &'static str {
        match func.return_val.as_ref() {
            Some(ret) if Self::loose_symbol_ffi_type(surface, ret) == "i32" => "status",
            _ => "status as i32",
        }
    }

    /// A `[status]` method: `Result<T, FlError>`, the trailing out-param becoming the
    /// Ok value (or () when the slot is status-only).
    fn write_status_method(
        out: &mut String,
        raw: Option<&str>,
        func: &Function,
        method: &str,
        slot: &str,
    ) -> Result<(), String> {
        let LoweredResult::Status { ok_ty, has_out } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::ExternalConsumer, func)?
        else {
            unreachable!("status emitter called for non-status slot")
        };
        let out_idx = Self::out_param_index(func);
        let LoweredArgs {
            params,
            ffi,
            prelude,
        } = Self::service_call_args(func, out_idx)?;
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn {}({}) -> Result<{}, crate::FlError> {{\n",
            method,
            Self::sig_with_self(&params),
            ok_ty
        ));
        for line in &prelude {
            out.push_str(&format!("        {}\n", line));
        }
        let call = Self::slot_call(raw, slot, &ffi);
        if has_out {
            out.push_str(&format!(
                "        let mut out = core::mem::MaybeUninit::<{}>::uninit();\n",
                ok_ty
            ));
            out.push_str(&format!("        let status = unsafe {{ {} }};\n", call));
            out.push_str(&format!(
                "        crate::FlError::from_status({})?;\n",
                Self::status_as_i32(LooseSymbolSurface::ExternalConsumer, func)
            ));
            out.push_str(&safety_assume_init("        ", "a success status"));
            out.push_str("        Ok(unsafe { out.assume_init() })\n");
        } else {
            out.push_str(&format!("        let status = unsafe {{ {} }};\n", call));
            out.push_str(&format!(
                "        crate::FlError::from_status({})?;\n",
                Self::status_as_i32(LooseSymbolSurface::ExternalConsumer, func)
            ));
            out.push_str("        Ok(())\n");
        }
        out.push_str("    }\n");
        Ok(())
    }

    /// A bool + out-param method: `Option<T>`, Some on the true status.
    fn write_option_method(
        out: &mut String,
        raw: Option<&str>,
        func: &Function,
        method: &str,
        slot: &str,
    ) -> Result<(), String> {
        let LoweredResult::Option { ty } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::ExternalConsumer, func)?
        else {
            unreachable!("option emitter called for non-option slot")
        };
        let out_idx = Self::out_param_index(func).expect("option shape guarantees out-param");
        let LoweredArgs {
            params,
            ffi,
            prelude,
        } = Self::service_call_args(func, Some(out_idx))?;
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn {}({}) -> Option<{}> {{\n",
            method,
            Self::sig_with_self(&params),
            ty
        ));
        for line in &prelude {
            out.push_str(&format!("        {}\n", line));
        }
        out.push_str(&format!(
            "        let mut out = core::mem::MaybeUninit::<{}>::uninit();\n",
            ty
        ));
        let call = Self::slot_call(raw, slot, &ffi);
        out.push_str(&format!("        if unsafe {{ {} }} {{\n", call));
        out.push_str(&safety_assume_init("            ", "true"));
        out.push_str("            Some(unsafe { out.assume_init() })\n");
        out.push_str("        } else {\n            None\n        }\n");
        out.push_str("    }\n");
        Ok(())
    }

    /// A `[transfer(free = ...)]` constructor method: returns the owning newtype
    /// (built from the raw pointer; its Drop calls the paired free symbol).
    fn write_transfer_method(
        out: &mut String,
        raw: Option<&str>,
        func: &Function,
        method: &str,
        slot: &str,
    ) -> Result<(), String> {
        let LoweredResult::Transfer { owned_ty: newtype } =
            Self::lower_loose_symbol_result(LooseSymbolSurface::ExternalConsumer, func)?
        else {
            unreachable!("transfer emitter called for non-transfer slot")
        };
        if func.transfer_free.is_none() {
            return Err(format!(
                "slot `{}`: a `[transfer]` return must name its destroy slot via \
                 `[transfer(free = <slot>)]`",
                func.name
            ));
        }
        let LoweredArgs {
            params,
            ffi,
            prelude,
        } = Self::service_call_args(func, None)?;
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn {}({}) -> {} {{\n",
            method,
            Self::sig_with_self(&params),
            newtype
        ));
        for line in &prelude {
            out.push_str(&format!("        {}\n", line));
        }
        let call = Self::slot_call(raw, slot, &ffi);
        out.push_str(&format!("        let ptr = unsafe {{ {} }};\n", call));
        out.push_str(&format!("        {} {{ ptr }}\n", newtype));
        out.push_str("    }\n");
        Ok(())
    }

    /// Emit an owning `Owned<T>` newtype for a `[transfer]` return: the raw pointer,
    /// with as_ptr/into_raw and a Drop that forwards to the paired destroy
    /// symbol. free_ptr_ty is the destroy slot's pointer-param type; Drop casts to
    /// it so a `*const`/`*mut` mismatch is a no-op cast, not a compile error.
    fn write_owned_newtype(
        out: &mut String,
        surface: LooseSymbolSurface,
        raw: Option<&str>,
        service: &str,
        ret: &Variable,
        free_slot: &str,
        free_ptr_ty: &str,
    ) {
        let newtype = Self::owned_newtype_name(&ret.type_name);
        let pointee = Self::loose_symbol_base_type(surface, ret);
        let ptr_ty = if ret.const_pointer {
            format!("*const {}", pointee)
        } else {
            format!("*mut {}", pointee)
        };
        out.push_str(&format!(
            "/// Owns the {} handed out by the {} service; Drop returns it to the\n\
             /// host via the exported {} symbol.\n",
            ret.type_name, service, free_slot
        ));
        out.push_str(&format!("pub struct {} {{\n", newtype));
        out.push_str(&format!("    ptr: {},\n", ptr_ty));
        out.push_str("}\n\n");
        out.push_str(&format!("impl {} {{\n", newtype));
        out.push_str("    /// The borrowed raw pointer (valid while self lives).\n");
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn as_ptr(&self) -> {} {{\n        self.ptr\n    }}\n\n",
            ptr_ty
        ));
        out.push_str(
            "    /// Take the raw pointer out, forgoing the Drop-time free (ownership moves\n\
             \x20   /// to the caller).\n",
        );
        out.push_str("    #[inline]\n");
        out.push_str(&format!(
            "    pub fn into_raw(self) -> {} {{\n        let ptr = self.ptr;\n        \
             core::mem::forget(self);\n        ptr\n    }}\n",
            ptr_ty
        ));
        out.push_str("}\n\n");
        let drop_arg = if ptr_ty == free_ptr_ty {
            "self.ptr".to_owned()
        } else {
            format!("self.ptr as {}", free_ptr_ty)
        };
        out.push_str(&format!("impl Drop for {} {{\n", newtype));
        out.push_str("    fn drop(&mut self) {\n");
        // Through the same slot_call every forwarding method uses: spelling it
        // unqualified here would not resolve in a module that forwards through a raw
        // bindings tree and so declares nothing itself.
        out.push_str(&format!(
            "        unsafe {{ {} }}\n",
            Self::slot_call(raw, &Self::rust_ident(free_slot), &[drop_arg])
        ));
        out.push_str("    }\n}\n\n");
    }

    /// Emit the full wrapper surface for one service api block (the exported-symbol
    /// extern "C" block, the wrapper struct, Send/Sync opt-in, owning newtypes,
    /// forwarding impl).
    fn write_service_api(
        out: &mut String,
        naming: &Naming,
        raw: Option<&str>,
        api: &Api,
        reads: Option<&ServiceReads>,
    ) -> Result<(), String> {
        let api_name = &api.name;
        let api_snake = api.name.to_snake_case();
        let surface = LooseSymbolSurface::ExternalConsumer;
        let generated = Self::service_generated_slots(api);

        let transfer_pairs = Self::validate_transfer_api(api)?;

        // 1. The exported symbols the service is reached through. Each non-varargs
        // slot is a plain extern "C" declaration linking the C symbol the exporting
        // library publishes under the slot's own name. A varargs slot has no linkable
        // Rust surface (stable Rust cannot call a C variadic) - C reaches it through a
        // macro, so it is omitted here and from the wrapper below.
        if let Some(path) = raw {
            out.push_str(&format!(
                "// The {} service, as plain C symbols the host exports. Their declarations\n\
                 // are the raw bindings in {}.\n\
                 // The safe {} wrapper below forwards each non-`[manual]` slot through them.\n\n",
                api_snake, path, api_name
            ));
        } else {
            out.push_str(&format!(
                "// The {} service, as plain C symbols the host exports. A consumer links\n\
                 // against them and calls them directly; the safe {} wrapper below forwards\n\
                 // each non-`[manual]` slot.\n",
                api_snake, api_name
            ));
            out.push_str("extern \"C\" {\n");
            for f in &api.functions {
                // `[manual]` slots stay declared - their hand-written adapters
                // call them. A `[c_only]` slot has no Rust caller at all.
                if f.has_varargs || f.is_c_only {
                    continue;
                }
                let (p, r) =
                    Self::loose_symbol_sig_parts(surface, &f.function_args, f.return_val.as_ref());
                Self::push_doc(out, &f.doc_comments, 4);
                out.push_str(&format!(
                    "    pub fn {}({}){};\n",
                    Self::rust_ident(&f.c_name),
                    p,
                    r
                ));
            }
            out.push_str("}\n\n");
        }

        // A block with no generated slot stops here: it has just declared its symbols,
        // which in a self-contained module is the only declaration of them. What it
        // must NOT get is the wrapper struct - a pub handle with a new() and no
        // method.
        if generated.is_empty() {
            return Ok(());
        }

        // 2. The safe wrapper. It carries no host pointer - the symbols are process-
        // global - yet the `PhantomData<*const ()>` keeps it !Send + !Sync by
        // default: a service's state may be thread-affine, so the wrapper does not
        // cross threads unless the service is audited thread_safe.
        out.push_str(&format!(
            "/// Safe consume-side wrapper over the {} service's exported symbols. Forwards\n\
             /// every non-`[manual]` slot. !Send + !Sync unless the service is\n\
             /// `#[attributes(service, thread_safe)]` or every slot is `[thread_safe]`.\n",
            api_snake
        ));
        out.push_str(&format!(
            "pub struct {} {{\n    _marker: PhantomData<*const ()>,\n}}\n\n",
            api_name
        ));

        // 3. Send + Sync opt-in - the whole service marked thread_safe, or every
        // generated slot individually so. !generated.is_empty() is not redundant with
        // the early return above: an empty "every slot is thread-safe" is not an audit.
        let send_sync = api.is_thread_safe
            || (!generated.is_empty() && generated.iter().all(|f| f.is_thread_safe));
        if send_sync {
            out.push_str(&format!(
                "// SAFETY: {} is audited thread-safe (thread_safe), so the wrapper may\n\
                 // cross threads.\n",
                api_name
            ));
            out.push_str(&format!("unsafe impl Send for {} {{}}\n", api_name));
            out.push_str(&format!("unsafe impl Sync for {} {{}}\n\n", api_name));
        }

        // 4. Owning newtypes for `[transfer]` returns (one per distinct pointee).
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        for (_, ret, free_fn) in transfer_pairs {
            if seen.insert(ret.type_name.clone()) {
                let free_ptr_ty = Self::loose_symbol_ffi_type(surface, &free_fn.function_args[0]);
                Self::write_owned_newtype(
                    out,
                    surface,
                    raw,
                    &api_snake,
                    ret,
                    &free_fn.c_name,
                    &free_ptr_ty,
                );
            }
        }

        // 5. The forwarding impl: a safe new() constructor + one method per
        // generated slot, each calling its exported symbol directly.
        out.push_str(&format!("impl {} {{\n", api_name));
        out.push_str(
            "    /// Construct the service wrapper. It holds no state - the symbols are\n    \
             /// process-global - so the only precondition its methods carry is the one\n    \
             /// every exported symbol carries: the exporting host is loaded and started.\n",
        );
        out.push_str("    #[inline]\n");
        out.push_str(
            "    pub const fn new() -> Self {\n        Self { _marker: PhantomData }\n    }\n",
        );
        for f in &generated {
            out.push('\n');
            Self::write_service_method(out, naming, raw, &api_snake, f, reads)?;
        }
        out.push_str("}\n\n");

        // A Default companion for the argument-free new() (repo convention, and
        // clears clippy's new_without_default).
        out.push_str(&format!(
            "impl Default for {} {{\n    #[inline]\n    fn default() -> Self {{\n        \
             Self::new()\n    }}\n}}\n\n",
            api_name
        ));
        Ok(())
    }

    /// Build the service-consume wrapper module text for a service def, or an
    /// Err(diagnostic) for the first unclassifiable slot (the hard-fail rule).
    /// Ok(None) when the def has no `#[attributes(service)]` block. Pure (no IO) so
    /// tests assert on the returned string.
    pub fn build_service_wrapper(
        api_def: &ApiDef,
        naming: &Naming,
        raw_path: Option<&str>,
        reads: Option<&ServiceReads>,
        script: &str,
    ) -> Result<Option<String>, String> {
        let service_apis: Vec<&Api> = api_def.apis.iter().filter(|a| a.is_service).collect();
        if service_apis.is_empty() {
            return Ok(None);
        }
        let any_generated = service_apis
            .iter()
            .any(|api| !Self::service_generated_slots(api).is_empty());
        // A def whose every slot is `[manual]` offers no method at all. Forwarding
        // through a raw bindings tree, the declarations are over there, so the module
        // would hold nothing but a method-less wrapper struct - skip it. Self-contained,
        // the module's own extern "C" block is the ONLY declaration of those symbols
        // anywhere and is what the hand-written adapters call, so it must be emitted.
        if !any_generated && raw_path.is_some() {
            return Ok(None);
        }
        let raw = raw_path.map(|p| format!("{}::{}", p, api_def.base_filename));
        // Only the wrapper struct uses it, and a declarations-only module has none.
        let mut body = if any_generated {
            String::from("use core::marker::PhantomData;\n\n")
        } else {
            String::new()
        };
        // extern opaque deps. A self-contained module declares its own uninhabited
        // enum per dep, exactly as the raw bindings backend does: its extern "C" block
        // names the type, so the declaration needs somewhere to point.
        //
        // A module forwarding through the raw tree must NOT mint a second one - the same
        // C type under two Rust spellings is what clashing_extern_declarations fires
        // on - but it cannot go without the name either: a slot returning an opaque
        // dep through a `[status]`/Option out-param never reaches the parameter guard,
        // and the method's own signature ends up naming the type. So the name is
        // imported from the raw tree instead of redeclared.
        //
        // The import goes out for every dep the def declares, used or not, which is what
        // the allow is for.
        for ext in &api_def.externs {
            match &raw {
                Some(path) => {
                    body.push_str("#[allow(unused_imports)]\n");
                    body.push_str(&format!("use {}::{};\n\n", path, ext.name));
                }
                None => {
                    for line in &ext.doc_comments {
                        body.push_str(&format!("/// {}\n", line));
                    }
                    body.push_str(&format!("pub enum {} {{}}\n\n", ext.name));
                }
            }
        }
        for api in service_apis {
            Self::write_service_api(&mut body, naming, raw.as_deref(), api, reads)?;
        }
        // A wrapper module is a declared FFI boundary by construction, so it states the
        // unsafe_code opt-out itself rather than making a consumer that denies
        // unsafe_code workspace-wide wrap the mod declaration in one.
        let mut out = Self::generated_header_with(&body, &["#![allow(unsafe_code)]"], script);
        out.push_str(&body);
        Ok(Some(out))
    }

    /// Emit the service-consume wrapper module for a service def into
    /// `wrapper_dir/<base>.rs`. Returns Ok(true) when a module was written,
    /// Ok(false) when the def is not a service. Panics with a clear diagnostic on an
    /// unclassifiable slot.
    pub fn generate_service_wrapper(
        wrapper_dir: &str,
        api_def: &ApiDef,
        naming: &Naming,
        raw_path: Option<&str>,
        reads: Option<&ServiceReads>,
        script: &str,
    ) -> io::Result<bool> {
        let module = match Self::build_service_wrapper(api_def, naming, raw_path, reads, script) {
            Ok(Some(m)) => m,
            Ok(None) => return Ok(false),
            Err(diag) => panic!(
                "api_gen: service wrapper `{}`: {}",
                api_def.base_filename, diag
            ),
        };
        let filename = format!("{}/{}.rs", wrapper_dir, api_def.base_filename);
        let mut f = BufWriter::new(File::create(&filename)?);
        write!(f, "{}", module)?;
        Ok(true)
    }

    /// Generate the external-consumer mod.rs index: one pub mod per emitted service
    /// wrapper. The shared runtime (FlError, the `fl_string_*` helpers the modules
    /// reference) is hand-written in the consumer crate, not generated here.
    pub fn generate_service_wrapper_mod_file(
        wrapper_dir: &str,
        modules: &[String],
        allow_dead_code: bool,
        script: &str,
    ) -> io::Result<()> {
        let filename = format!("{}/mod.rs", wrapper_dir);
        let mut f = BufWriter::new(File::create(&filename)?);
        write!(f, "{}", crate::emit_util::header(script))?;
        writeln!(f)?;
        Self::write_mirror_allow(&mut f, allow_dead_code)?;
        for m in modules {
            writeln!(f, "pub mod {};", m)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::{ApiDef, ApiParser};
    use std::process::Command;

    /// rustc if present (else the test skips), for compiling generated bindings.
    fn find_rustc() -> Option<&'static str> {
        Command::new("rustc")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
            .then_some("rustc")
    }

    /// Compile a standalone Rust snippet as a library (metadata-only, no codegen)
    /// and report whether it built. tag keeps the temp path unique per case.
    fn rustc_compiles(rustc: &str, tag: &str, src: &str) -> bool {
        let dir = std::env::temp_dir();
        let path = dir.join(format!("api_gen_rs_{}_{}.rs", std::process::id(), tag));
        std::fs::write(&path, src).expect("write temp rs");
        let status = Command::new(rustc)
            .args([
                "--crate-type=lib",
                "--edition=2021",
                "--emit=metadata",
                "-o",
            ])
            .arg(dir.join(format!("api_gen_rs_{}_{}.rmeta", std::process::id(), tag)))
            .arg(&path)
            .status()
            .expect("run rustc");
        let _ = std::fs::remove_file(&path);
        status.success()
    }

    /// Drop a generated module's file-scoped preamble - the // @generated banner,
    /// the shared //! SAFETY: statement and any `#![...]` attribute. Tests that
    /// compile generated output splice it after stand-in stubs, where file-scoped
    /// items would no longer be legal.
    fn strip_file_header(out: &str) -> String {
        out.lines()
            .skip_while(|l| {
                l.trim().is_empty()
                    || l.starts_with("//!")
                    || l.starts_with("#![")
                    || l.starts_with("// @generated")
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn parse_one(defs: &str, file: &str) -> ApiDef {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(defs, file, &mut api_def);
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        api_def
    }

    /// A `#[attributes(service)]` api block emits the same extern "C" binding as any
    /// other api block, except its slots link the raw exported symbol
    /// (arena_rewind) since a service slot bakes the domain into its own name. The
    /// same api without the marker re-prefixes to fl_arena_rewind.
    #[test]
    fn service_api_emits_extern_with_raw_slot_name() {
        let dir = std::env::temp_dir().join(format!("api_gen_svc_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let dir_s = dir.to_str().unwrap();

        let svc = parse_one(
            "#[attributes(Opaque)] struct Arena {}\n\
             #[attributes(service)] api Arena { arena_rewind(arena: *Arena) }",
            "arena.def",
        );
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&svc));
        RustGen::generate(dir_s, &svc, &reg, "scripts/gen.sh").expect("generate svc");
        let svc_rs = std::fs::read_to_string(dir.join("arena.rs")).expect("read svc rs");
        assert!(
            svc_rs.contains("extern \"C\" {")
                && svc_rs.contains("pub fn arena_rewind(arena: *mut crate::Arena);"),
            "a service api emits an extern block naming the raw slot symbol: {svc_rs}"
        );
        assert!(
            !svc_rs.contains("pub struct ArenaApi {"),
            "a service api emits no vtable ABI mirror: {svc_rs}"
        );
        assert!(
            svc_rs.contains("pub enum Arena {}"),
            "the def's data types still emit for a service def: {svc_rs}"
        );

        let plain = parse_one(
            "#[attributes(Opaque)] struct Arena {}\n\
             api Arena { rewind(arena: *Arena) }",
            "arena.def",
        );
        let reg2 = crate::layout::TypeRegistry::build(std::slice::from_ref(&plain));
        RustGen::generate(dir_s, &plain, &reg2, "scripts/gen.sh").expect("generate plain");
        let plain_rs = std::fs::read_to_string(dir.join("arena.rs")).expect("read plain rs");
        assert!(
            plain_rs.contains("pub fn fl_arena_rewind(arena: *mut crate::Arena);"),
            "a non-service api re-prefixes to the fl_<domain>_<slot> spelling: {plain_rs}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A `[retained]` slot's façade copies its `*const T` arg into wrapper-owned static
    /// storage and passes C a pointer to that copy - so a safe caller may pass a stack
    /// temporary - while keeping the &T signature.
    #[test]
    fn retained_marker_copies_const_ptr_arg_into_owned_storage() {
        let dir = std::env::temp_dir().join(format!("api_gen_ret_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let api_def = parse_one(
            "struct ThemeColors { x: f32 }\n\
             api Theme {\n\
                 [retained] update(colors: *const ThemeColors)\n\
                 peek(colors: *const ThemeColors)\n\
             }",
            "theme.def",
        );
        assert!(
            RustGen::generate_facade(dir.to_str().unwrap(), &api_def, "scripts/gen.sh")
                .expect("facade")
        );
        let out = std::fs::read_to_string(dir.join("theme.rs")).expect("read facade");

        // Both slots keep the ergonomic borrow signature - callers are unaffected.
        assert!(
            out.contains("pub fn update(colors: &flowi_sys::ThemeColors)"),
            "retained slot keeps the &T signature: {out}"
        );
        // The retained slot copies into a fn-local static and passes that copy.
        assert!(
            out.contains(
                "static mut RETAINED_COLORS: core::mem::MaybeUninit<flowi_sys::ThemeColors>"
            ),
            "wrapper-owned static storage: {out}"
        );
        assert!(
            out.contains("core::ptr::copy_nonoverlapping(colors as *const flowi_sys::ThemeColors, colors_owned, 1);"),
            "the copy precedes the call: {out}"
        );
        assert!(
            out.contains(
                "flowi_sys::fl_theme_update(colors_owned as *const flowi_sys::ThemeColors)"
            ),
            "C receives the owned copy's pointer: {out}"
        );
        // The unmarked slot still passes the caller's borrow straight through.
        assert!(
            out.contains("flowi_sys::fl_theme_peek(colors as *const flowi_sys::ThemeColors)"),
            "unmarked slot keeps pass-the-borrow: {out}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A `mod <name>` directive emits `use crate::<name>::*;` at the top of the
    /// binding, one per directive in order, so a signature can name a payload type the
    /// sibling module defines.
    #[test]
    fn mod_emits_use_import_and_compiles() {
        let api_def = parse_one(
            "#[module(render)]\nmod render_ir\nmod image\nstruct Backend { frame: *RenderFrame }",
            "backend.def",
        );
        let mut buf = Vec::new();
        RustGen::generate_mod_imports(&mut buf, &api_def).expect("emit imports");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(out.contains("use crate::render_ir::*;"), "first mod import");
        assert!(out.contains("use crate::image::*;"), "second mod import");

        let plain = parse_one("struct Plain { x: f32 }", "plain.def");
        let mut pbuf = Vec::new();
        RustGen::generate_mod_imports(&mut pbuf, &plain).expect("emit");
        assert!(pbuf.is_empty(), "no mod => no import lines");

        let Some(rustc) = find_rustc() else {
            eprintln!("mod import rust compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "pub mod render_ir {{ pub struct FlRenderFrame; }}\npub mod image {{}}\n{}",
            out
        );
        assert!(
            rustc_compiles(rustc, "mod_import", &src),
            "mod imports must compile"
        );
    }

    /// A handle becomes a `#[repr(transparent)]` newtype over its underlying int with
    /// an INVALID sentinel const + size assertion.
    #[test]
    fn handle_newtype_emits_transparent_with_sentinel_and_compiles() {
        let api_def = parse_one(
            "#[handle(u32, invalid = 0xFFFFFFFF)]\nstruct ImageHandle {}",
            "image_handle.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "ImageHandle")
            .expect("parsed");
        let mut buf = Vec::new();
        RustGen::generate_handle_newtype(&mut buf, sdef).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("#[repr(transparent)]"),
            "transparent over the int"
        );
        assert!(
            out.contains("pub struct ImageHandle(pub u32);"),
            "newtype over u32"
        );
        assert!(
            out.contains("pub const INVALID: Self = Self(0xFFFFFFFF);"),
            "INVALID sentinel const"
        );
        assert!(
            out.contains("size_of::<ImageHandle>() == 4"),
            "size pinned to the int width"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("handle rust compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "handle", &out),
            "the handle newtype must compile"
        );
    }

    /// `#[attributes(serde)]` adds the serde derives behind the consuming crate's
    /// serde feature; without it the derive line is untouched.
    #[test]
    fn the_serde_attribute_gates_its_derives_on_the_consumers_feature() {
        let emit = |src: &str| {
            let api_def = parse_one(src, "demozoo.def");
            let mut buf = Vec::new();
            RustGen::generate_data_enum(&mut buf, &api_def.enums[0]).expect("emit");
            String::from_utf8(buf).expect("utf8")
        };

        let out = emit("#[attributes(serde)]\nenum Supertype {\n    Any = 0,\n    Music = 1,\n}");
        assert!(out.contains(
            "#[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
             #[cfg_attr(feature = \"serde\", derive(serde::Serialize, serde::Deserialize))]\n\
             pub enum Supertype {"
        ));

        assert!(!emit("enum Supertype {\n    Any = 0,\n    Music = 1,\n}").contains("serde"));
    }

    /// A `#[attributes(Copy, Default)]` config struct adds Default to the derive set
    /// so it can be built with ..Default::default().
    #[test]
    fn default_attribute_adds_default_derive_and_compiles() {
        let api_def = parse_one(
            "#[attributes(Copy, Default)]\nstruct MenuConfig { min_width: f32, z_index: i16 }",
            "menu.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "MenuConfig")
            .expect("parsed");
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        RustGen::generate_data_struct(&mut buf, sdef, &reg).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("#[derive(Copy, Clone, Debug, Default)]"),
            "Default joins the Copy derive set: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("default-derive rust compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!("{out}\npub fn build() -> MenuConfig {{ MenuConfig {{ z_index: 5, ..Default::default() }} }}\n");
        assert!(
            rustc_compiles(rustc, "default_derive", &src),
            "the Default-deriving struct must compile"
        );
    }

    /// Without the Default attribute, a plain `#[attributes(Copy)]` struct keeps the
    /// exact Copy, Clone, Debug derive line, so regeneration stays a no-op.
    #[test]
    fn copy_without_default_attribute_omits_default_derive() {
        let api_def = parse_one(
            "#[attributes(Copy)]\nstruct Plain { a: f32, b: i16 }",
            "plain.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "Plain")
            .expect("parsed");
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        RustGen::generate_data_struct(&mut buf, sdef, &reg).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("#[derive(Copy, Clone, Debug)]"),
            "the unchanged Copy derive line"
        );
        assert!(
            !out.contains("Default"),
            "no Default derive without the attribute"
        );
    }

    /// An opaque type becomes an uninhabited enum, usable only behind a pointer.
    #[test]
    fn opaque_type_emits_uninhabited_enum_and_compiles() {
        let api_def = parse_one(
            "#[attributes(Opaque)]\nstruct TextInputState {}",
            "text_input.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "TextInputState")
            .expect("parsed");
        let mut buf = Vec::new();
        RustGen::generate_opaque_type(&mut buf, sdef).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("pub enum TextInputState {}"),
            "uninhabited opaque enum"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("opaque rust compile test skipped: no rustc on PATH");
            return;
        };
        // Used behind a pointer, never by value (it is uninhabited).
        let src = format!(
            "{}\npub fn use_it(p: *mut TextInputState) -> bool {{ !p.is_null() }}\n",
            out
        );
        assert!(
            rustc_compiles(rustc, "opaque", &src),
            "the opaque enum must compile and support pointer use"
        );
    }

    /// A status code added to the def yields a named FlError variant with a literal
    /// decode arm, so the drift path where a new code silently decodes to Unknown is
    /// closed by regeneration. The code-0 entry stays excluded, the catch-all last.
    #[test]
    fn error_enum_added_code_yields_named_variant() {
        let def = |extra: &str| {
            format!(
                "#[attributes(error_enum)]\n\
                 enum Status {{\n\
                 \x20   /// The operation succeeded.\n\
                 \x20   Success = 0,\n\
                 \x20   /// Generic invalid argument.\n\
                 \x20   InvalidArgument = 1,\n\
                 {}}}",
                extra
            )
        };
        let emit = |src: &str| {
            let api_def = parse_one(src, "status.def");
            let edef = api_def
                .enums
                .iter()
                .find(|e| e.name == "Status")
                .expect("parsed");
            assert!(edef.is_error_enum, "attribute sets the flag");
            let mut buf = Vec::new();
            RustGen::generate_error_enum(&mut buf, edef).expect("emit");
            String::from_utf8(buf).expect("utf8")
        };

        let before = emit(&def(""));
        assert!(
            !before.contains("VfsNotMounted"),
            "the new code is not yet in the def"
        );

        let out = emit(&def(
            "    /// The path has no mount.\n    VfsNotMounted = 500,\n",
        ));
        assert!(
            out.contains("    VfsNotMounted,"),
            "added code gets a named variant: {out}"
        );
        assert!(
            out.contains("            500 => FlError::VfsNotMounted,"),
            "added code gets a literal decode arm: {out}"
        );
        assert!(
            out.contains("/// The path has no mount."),
            "the def's doc comment rides along: {out}"
        );
        assert!(
            !out.contains("\n    Success,"),
            "the code-0 success entry is the Ok arm, never a variant: {out}"
        );
        assert!(
            out.contains("Unknown(i32),") && out.contains("other => FlError::Unknown(other),"),
            "the catch-all survives: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("error_enum compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "#[repr(C)]\n#[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
             pub enum Status {{ Success = 0, InvalidArgument = 1, VfsNotMounted = 500 }}\n{}",
            out
        );
        assert!(
            rustc_compiles(rustc, "error_enum", &src),
            "generated FlError must compile standalone"
        );
    }

    /// error_enum hard-fails on a def with no code-0 success entry - there is
    /// nothing to make the Ok arm of from_status.
    #[test]
    fn error_enum_requires_success_zero() {
        let api_def = parse_one(
            "#[attributes(error_enum)]\nenum Status {\n    InvalidArgument = 1,\n}",
            "status.def",
        );
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == "Status")
            .expect("parsed");
        let mut buf = Vec::new();
        let err = RustGen::generate_error_enum(&mut buf, edef)
            .expect_err("missing code-0 success must fail");
        assert!(
            err.to_string().contains("success"),
            "names the missing success entry: {err}"
        );
    }

    /// A bitflags set emits the fully-qualified bitflags::bitflags! macro - no use
    /// is generated, so an unqualified call would not compile.
    #[test]
    fn bitflags_emits_qualified_macro_transparent_and_size_assert() {
        let api_def = parse_one(
            "#[attributes(bitflags)]\nenum Flags {\n    a = 1,\n    b = 2,\n    c = 4,\n}",
            "flags.def",
        );
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == "Flags")
            .expect("parsed");
        let mut buf = Vec::new();
        RustGen::generate_bitflags(&mut buf, edef).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("bitflags::bitflags! {"),
            "qualified macro path"
        );
        assert!(
            !out.contains("\nbitflags! {"),
            "must not emit an unqualified macro call"
        );
        assert!(
            out.contains("#[repr(transparent)]"),
            "transparent over the u32"
        );
        assert!(
            out.contains("#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]"),
            "the flag set carries the standard derives"
        );
        assert!(
            out.contains("pub struct Flags: u32 {"),
            "spelled by the unprefixed name"
        );
        assert!(
            out.contains("const A = 1;") && out.contains("const C = 4;"),
            "SHOUTY consts (a -> A)"
        );
        assert!(
            out.contains("size_of::<Flags>() == 4"),
            "size pinned to u32 width"
        );
    }

    /// An or-list flag (All = A | B) emits as a real const with its OR'd integer
    /// value, not silently dropped; a nested or-list (AllC = All | C) resolves
    /// recursively through it.
    #[test]
    fn or_list_flag_emits_combined_value() {
        let api_def = parse_one(
            "#[attributes(bitflags)]\n\
             enum Flags {\n    None = 0,\n    A = 1,\n    B = 2,\n    C = 4,\n    All = A | B,\n    AllC = All | C,\n}",
            "flags.def",
        );
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == "Flags")
            .expect("parsed");
        let mut buf = Vec::new();
        RustGen::generate_bitflags(&mut buf, edef).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("const A = 1;"),
            "plain-valued flags are unaffected: {out}"
        );
        assert!(
            out.contains("const ALL = 3;"),
            "the or-list flag emits its combined value, not dropped: {out}"
        );
        assert!(
            out.contains("const ALL_C = 7;"),
            "a nested or-list resolves through the referenced or-list: {out}"
        );
    }

    /// A plain `#[repr(C)]` data enum with an or-list entry emits the combined value
    /// too, and - unlike a bitflags set - compiles standalone with no external crate.
    #[test]
    fn or_list_data_enum_emits_and_compiles() {
        let api_def = parse_one(
            "enum Combo {\n    A = 1,\n    B = 2,\n    AB = A | B,\n}",
            "combo.def",
        );
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == "Combo")
            .expect("parsed");
        let mut buf = Vec::new();
        RustGen::generate_data_enum(&mut buf, edef).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("AB = 3,"),
            "the or-list entry emits its combined value: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("or-list data-enum compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!("{}\npub fn use_ab() -> Combo {{ Combo::AB }}\n", out);
        assert!(
            rustc_compiles(rustc, "or_list_data_enum", &src),
            "generated or-list data enum must compile"
        );
    }

    /// A bad or-list reference fails generation through rust_gen's own emit site (its
    /// map_err into an io::Error) rather than dropping the entry.
    #[test]
    fn or_list_undefined_reference_errors() {
        let api_def = parse_one(
            "enum Combo {\n    A = 1,\n    Bad = A | Missing,\n}",
            "combo.def",
        );
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == "Combo")
            .expect("parsed");
        let mut buf = Vec::new();
        let res = RustGen::generate_data_enum(&mut buf, edef);
        assert!(
            res.is_err(),
            "an undefined or-list reference must fail rust generation, got: {:?}",
            String::from_utf8(buf)
        );
        let msg = res.unwrap_err().to_string();
        assert!(
            msg.contains("Missing") && msg.contains("undefined"),
            "the error names the undefined enumerator: {msg}"
        );
    }

    /// Pointer-primitive fields spell to `core::ffi::*`; a referenced opaque type
    /// crosses as `*mut crate::<Name>` - a typed pointer to the uninhabited enum, not
    /// a c_void.
    #[test]
    fn pointer_primitive_and_opaque_rust_spellings() {
        let api_def = parse_one(
            "#[attributes(Opaque)]\nstruct Arena {}\nstruct Span { text: *const char, scratch: *void, arena: *Arena }",
            "span.def",
        );
        let span = api_def
            .structs
            .iter()
            .find(|s| s.name == "Span")
            .expect("parsed");
        let vars = &span.variables;
        assert_eq!(
            RustGen::rust_field_type(&vars[0]),
            "*const core::ffi::c_char"
        );
        assert_eq!(RustGen::rust_field_type(&vars[1]), "*mut core::ffi::c_void");
        assert_eq!(RustGen::rust_field_type(&vars[2]), "*mut crate::Arena");

        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        RustGen::generate_data_struct(&mut buf, span, &reg).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("pub text: *const core::ffi::c_char,"),
            "const char* field"
        );
        assert!(
            out.contains("pub scratch: *mut core::ffi::c_void,"),
            "void* field"
        );
        assert!(
            out.contains("pub arena: *mut crate::Arena,"),
            "opaque type as typed crate pointer"
        );
    }

    /// A fixed-size array field emits `pub name: [u8; 24],`.
    #[test]
    fn fixed_array_field_emits_and_compiles() {
        let api_def = parse_one(
            "struct Cell { name: [u8; 24], scope_width: u8 }",
            "cell.def",
        );
        let cell = api_def
            .structs
            .iter()
            .find(|s| s.name == "Cell")
            .expect("parsed");
        assert_eq!(RustGen::rust_field_type(&cell.variables[0]), "[u8; 24]");

        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        RustGen::generate_data_struct(&mut buf, cell, &reg).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("pub name: [u8; 24],"),
            "fixed array field: {}",
            out
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("fixed-array rust compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "fixed_array", &out),
            "fixed-array struct + layout assert must compile"
        );
    }

    /// A struct with function-fields mirrors each as a nullable
    /// `Option<unsafe extern "C" fn(args) -> ret>` slot, with a layout assertion
    /// pinning every slot at its 8-byte-stride offset; each extern opaque dep emits a
    /// module-local uninhabited enum named verbatim, referenced as `*mut <Name>`.
    #[test]
    fn struct_function_fields_emit_option_extern_fn_mirror_and_compile() {
        let api_def = parse_one(
            "extern opaque UiCtx\n\
             extern opaque FlArena\n\
             struct Backend {\n\
                 ctx: *void,\n\
                 destroy(ctx: *void),\n\
                 poll(ctx: *void, ui: *UiCtx) -> bool,\n\
                 clip(ctx: *void, arena: *FlArena),\n\
                 on_job: bool,\n\
             }",
            "backend.def",
        );
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        for ext in &api_def.externs {
            RustGen::generate_extern_opaque_type(&mut buf, ext).expect("extern emit");
        }
        let backend = api_def
            .structs
            .iter()
            .find(|s| s.name == "Backend")
            .expect("struct");
        RustGen::generate_data_struct(&mut buf, backend, &reg).expect("struct emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(out.contains("pub enum UiCtx {}"), "UiCtx ZST");
        assert!(out.contains("pub enum FlArena {}"), "FlArena ZST");
        assert!(
            out.contains(
                "pub destroy: Option<unsafe extern \"C\" fn(ctx: *mut core::ffi::c_void)>,"
            ),
            "void fn-field: {out}"
        );
        assert!(
            out.contains("pub poll: Option<unsafe extern \"C\" fn(ctx: *mut core::ffi::c_void, ui: *mut UiCtx) -> bool>,"),
            "extern-opaque ptr arg + bool return: {out}"
        );
        assert!(
            out.contains("arena: *mut FlArena"),
            "extern-opaque arg is a bare *mut, not crate::"
        );
        // The trailing on_job value field is emitted AFTER the function-pointer
        // slots, not hoisted ahead of them, so it lands at offset 32 (ctx + 3 fn
        // slots); a reorder to variables-then-functions would put it at offset 8.
        assert!(
            out.contains("pub on_job: bool,"),
            "trailing value field emitted: {out}"
        );
        assert!(
            out.find("pub on_job: bool,") > out.find("pub clip:"),
            "trailing value field emitted after the fn-fields: {out}"
        );
        assert!(
            out.contains("size_of::<Backend>() == 40"),
            "four pointer slots + padded bool"
        );
        assert!(
            out.contains("offset_of!(Backend, poll) == 16"),
            "fn-field offset pinned"
        );
        assert!(
            out.contains("offset_of!(Backend, on_job) == 32"),
            "trailing value field offset pinned"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("vtable mirror compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "vtable_mirror", &out),
            "the Option<unsafe extern fn> mirror + layout assert must compile"
        );
    }

    /// A C anonymous union field (member name omitted) has no Rust equivalent, so it
    /// maps to a synthetic payload field of a `<Struct>Payload` union type, and the
    /// layout assertion pins that field under payload (not the empty C name). A
    /// keyword arm (move) is raw-escaped.
    #[test]
    fn anonymous_union_emits_payload_field_and_compiles() {
        let api_def = parse_one(
            "#[attributes(Copy)]\nstruct MoveData { x: f32, y: f32 }\n\
             #[attributes(Copy)]\nstruct WheelData { x: f32, y: f32 }\n\
             #[attributes(Copy)]\nstruct PtrEvent { kind: u32, union { move: MoveData, wheel: WheelData }, stamp: u64 }",
            "ptr.def",
        );
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            RustGen::generate_data_struct(&mut buf, s, &reg).expect("emit");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("pub union PtrEventPayload {"),
            "anon union -> <Struct>Payload type: {out}"
        );
        assert!(
            out.contains("pub r#move: crate::MoveData,"),
            "keyword arm raw-escaped: {out}"
        );
        assert!(
            out.contains("pub payload: PtrEventPayload,"),
            "synthetic payload field: {out}"
        );
        // The offset is pinned under payload, never an empty name - an empty one made
        // the generated binding fail to compile.
        assert!(
            out.contains("offset_of!(PtrEvent, payload)"),
            "payload offset pinned: {out}"
        );
        assert!(
            !out.contains("offset_of!(PtrEvent, )"),
            "no empty-name offset_of: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("anon-union rust emit compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "anon_union_rust", &out),
            "the payload union + layout assert must compile"
        );
    }

    /// A C field named self, super, or crate - reserved path-relative keywords
    /// rustc rejects as raw identifiers - is emitted with a trailing underscore
    /// (self_), while type still raw-escapes and the layout guard names the same
    /// escaped idents.
    #[test]
    fn path_keyword_fields_escape_with_underscore_and_compile() {
        let api_def = parse_one(
            "#[attributes(Copy)]\nstruct Keywords { self: u32, super: u32, crate: u32, type: u32, x: f32 }",
            "keywords.def",
        );
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let mut buf = Vec::new();
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            RustGen::generate_data_struct(&mut buf, s, &reg).expect("emit");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(out.contains("pub self_: u32,"), "self -> self_: {out}");
        assert!(out.contains("pub super_: u32,"), "super -> super_: {out}");
        assert!(out.contains("pub crate_: u32,"), "crate -> crate_: {out}");
        assert!(
            !out.contains("r#self") && !out.contains("r#super") && !out.contains("r#crate"),
            "no r# form for path keywords: {out}"
        );
        assert!(out.contains("pub r#type: u32,"), "type still r#type: {out}");
        assert!(
            out.contains("offset_of!(Keywords, self_)"),
            "layout guard names self_: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("path-keyword rust emit compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "path_keyword_rust", &out),
            "the escaped struct + layout assert must compile"
        );
    }

    /// A `callback <Name>` emits a nullable fn-pointer type alias, usable as a struct
    /// field (`crate::<Name>`, sized as an 8-byte fn-pointer slot) and as an api-fn arg.
    #[test]
    fn callback_emits_nullable_alias_usable_as_field_and_arg() {
        let api_def = parse_one(
            "extern opaque FlVfsEntry\n\
             callback VfsListingCallback(user_data: *void, entry: *const FlVfsEntry) -> bool\n\
             struct Pipe { on_list: VfsListingCallback, tag: u32 }\n\
             api Lister { scan(cb: VfsListingCallback) }",
            "vfs_listing.def",
        );
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));

        let mut buf = Vec::new();
        for ext in &api_def.externs {
            RustGen::generate_extern_opaque_type(&mut buf, ext).expect("ext");
        }
        RustGen::generate_callback_alias(&mut buf, &api_def.callbacks[0]).expect("alias");
        let pipe = api_def
            .structs
            .iter()
            .find(|s| s.name == "Pipe")
            .expect("struct");
        RustGen::generate_data_struct(&mut buf, pipe, &reg).expect("struct");
        RustGen::generate_api_externs(&mut buf, &api_def.apis[0]).expect("externs");
        let out = String::from_utf8(buf).expect("utf8");

        // Param names included, exactly like the struct fn-field mirror.
        assert!(
            out.contains("pub type VfsListingCallback = Option<unsafe extern \"C\" fn(user_data: *mut core::ffi::c_void, entry: *const FlVfsEntry) -> bool>;"),
            "nullable fn-pointer alias: {out}"
        );
        assert!(
            out.contains("pub on_list: crate::VfsListingCallback,"),
            "callback as a struct field: {out}"
        );
        assert!(
            out.contains("size_of::<Pipe>() == 16"),
            "8-byte fn-pointer + u32 padded to 16"
        );
        assert!(
            out.contains("offset_of!(Pipe, tag) == 8"),
            "tag follows the 8-byte fn-pointer slot"
        );
        assert!(
            out.contains("pub fn fl_lister_scan(cb: crate::VfsListingCallback);"),
            "callback as an api arg: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("callback rust compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "callback_alias", &out),
            "the callback alias + field struct + extern must compile"
        );
    }

    /// An `api <Domain>` block emits an extern "C" block of direct `fl_*`
    /// declarations for a normal domain (cursor); a varargs-only domain (format) emits
    /// nothing, since stable Rust cannot call a C variadic.
    #[test]
    fn api_externs_compile_and_are_callable() {
        let cursor = parse_one(
            "enum CursorShape { Arrow = 0, Text = 6, }\n\
             #[attributes(Copy)]\n\
             struct Cursor { shape: CursorShape }\n\
             api Cursor {\n\
                 set(cursor: Cursor)\n\
                 get_requested() -> Cursor\n\
                 set_visible(visible: bool)\n\
                 get_visible() -> bool\n\
             }",
            "cursor.def",
        );
        let format = parse_one(
            "api Format { frame_string(fmt: *const char, ...) -> String }",
            "format.def",
        );

        let mut buf = Vec::new();
        RustGen::generate_api_externs(&mut buf, &cursor.apis[0]).expect("cursor externs");
        RustGen::generate_api_externs(&mut buf, &format.apis[0]).expect("format externs");
        let externs = String::from_utf8(buf).expect("utf8");

        assert!(externs.contains("extern \"C\" {"), "extern block");
        assert!(
            externs.contains("pub fn fl_cursor_set(cursor: crate::Cursor);"),
            "a function over the generated data type"
        );
        assert!(
            externs.contains("pub fn fl_cursor_get_requested() -> crate::Cursor;"),
            "a no-arg returning fn"
        );
        assert!(
            externs.contains("pub fn fl_cursor_get_visible() -> bool;"),
            "a bool fn"
        );
        assert!(
            !externs.contains("CursorAPI"),
            "no fn-pointer vtable struct"
        );
        assert!(!externs.contains("g_fl_ui"), "no composed root");
        assert!(
            !externs.contains("FormatAPI"),
            "no varargs placeholder type"
        );
        assert!(
            !externs.contains("fl_format_frame_string"),
            "varargs fn is not Rust-callable"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("api externs compile test skipped: no rustc on PATH");
            return;
        };

        // --emit=metadata does not link, so the unresolved externs are fine.
        let src = format!(
            "#![allow(improper_ctypes)]\n\
             #[repr(C)] #[derive(Copy, Clone)] pub struct Cursor {{ pub shape: u32 }}\n\
             {externs}\n\
             pub fn set(c: Cursor) {{ unsafe {{ fl_cursor_set(c) }} }}\n\
             pub fn visible() -> bool {{ unsafe {{ fl_cursor_get_visible() }} }}\n",
            externs = externs,
        );
        assert!(
            rustc_compiles(rustc, "api_externs", &src),
            "the generated extern fns must compile and be callable directly"
        );
    }

    /// The façade emitter turns each `api <Domain>` block into `impl <Domain>` of
    /// methods forwarding to `flowi_sys::fl_*`, applying the mechanical conversions
    /// (string -> `impl AsRef<str>` + arena, `#[handle]` passthrough, LayoutId ->
    /// `impl Into<LayoutId>` + .into().into_sys(), `*T` -> &mut T), while `[manual]` and
    /// varargs slots are skipped.
    #[test]
    fn facade_emits_forwarding_methods_with_conversions() {
        let def = parse_one(
            "#[handle(u32, invalid = 0)]\nstruct FontId {}\n\
             api Painter {\n\
                 rect(x: f32, y: f32, color: Color)\n\
                 text(x: f32, y: f32, text: String, font: FontId)\n\
                 image(image: FontId) -> bool\n\
                 [manual] raw(p: *void)\n\
             }\n\
             api UiMenu {\n\
                 begin_impl(menu_id: LayoutId, value: *f32) -> bool\n\
                 end_impl()\n\
             }",
            "painter.def",
        );
        let mut buf = Vec::new();
        // generate_facade writes a file; emit the per-block impls directly into a
        // buffer instead so the test needs no temp dir.
        for api in &def.apis {
            writeln!(buf, "pub struct {};", api.name).unwrap();
            writeln!(buf, "impl {} {{", api.name).unwrap();
            for func in api
                .functions
                .iter()
                .filter(|f| RustGen::facade_generates(f))
            {
                RustGen::generate_facade_fn(&mut buf, func).unwrap();
            }
            writeln!(buf, "}}").unwrap();
        }
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("pub struct Painter;"), "domain struct");
        assert!(out.contains("impl Painter {"), "domain impl");
        assert!(
            out.contains("pub fn rect(x: f32, y: f32, color: flowi_sys::Color)"),
            "primitive + data arg: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_painter_rect(x, y, color)"),
            "direct call path"
        );
        assert!(
            out.contains(
                "pub fn text(x: f32, y: f32, text: impl AsRef<str>, font: flowi_sys::FontId)"
            ),
            "string + handle args"
        );
        assert!(
            out.contains("{ let s = text.as_ref(); flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()) }, font)"),
            "string arena + handle passthrough"
        );
        assert!(
            out.contains("pub fn image(image: flowi_sys::FontId) -> bool"),
            "handle arg + bool return"
        );
        assert!(!out.contains("fn raw"), "manual slot skipped");
        assert!(
            out.contains("pub fn begin(menu_id: impl Into<crate::LayoutId>) -> Option<f32>"),
            "LayoutId + option out-param, _impl stripped: {out}"
        );
        assert!(
            out.contains(
                "flowi_sys::fl_ui_menu_begin_impl(menu_id.into().into_sys(), out.as_mut_ptr())"
            ),
            "c_name keeps _impl; out-param is lifted"
        );
        assert!(
            out.contains("pub fn end()"),
            "no-arg method, _impl stripped"
        );
    }

    /// A slot taking a pointer to an extern opaque dep gets no safe façade method -
    /// the dep is an uninhabited enum, so no safe caller can ever produce the &mut
    /// the wrapper would demand. Keyed off the extern-opaque property, not the name.
    #[test]
    fn facade_skips_slots_taking_extern_opaque_pointer() {
        let def = parse_one(
            "extern opaque FlVfsMount\n\
             api Icon {\n\
                 get(icon: u32) -> u32\n\
                 load(mount: *FlVfsMount)\n\
             }",
            "icon.def",
        );
        let api = &def.apis[0];
        let load = api.functions.iter().find(|f| f.name == "load").unwrap();
        let get = api.functions.iter().find(|f| f.name == "get").unwrap();
        assert!(load.function_args[0].is_extern_opaque, "parser flags mount");
        assert!(
            !RustGen::facade_generates(load),
            "extern-opaque arg slot must not get a safe façade wrapper"
        );
        assert!(
            !RustGen::raii_generates(load),
            "extern-opaque arg slot must not get an RAII method either"
        );
        assert!(
            RustGen::facade_generates(get),
            "sibling slot without extern-opaque args still generates"
        );
        let mut buf = Vec::new();
        RustGen::generate_api_externs(&mut buf, api).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(
            out.contains("pub fn fl_icon_load(mount: *mut FlVfsMount);"),
            "raw flowi_sys extern unchanged: {out}"
        );
    }

    // The const-pointer arg path (`*const T` -> &T + `as *const T`) is a real emitter
    // behaviour that no currently-generated .def slot happens to exercise.
    #[test]
    fn facade_emits_const_pointer_arg() {
        let def = parse_one(
            "api Painter {\n\
                 peek(p: *const Color)\n\
             }",
            "painter.def",
        );
        let mut buf = Vec::new();
        for api in &def.apis {
            for func in api
                .functions
                .iter()
                .filter(|f| RustGen::facade_generates(f))
            {
                RustGen::generate_facade_fn(&mut buf, func).unwrap();
            }
        }
        let out = String::from_utf8(buf).unwrap();

        assert!(
            out.contains("pub fn peek(p: &flowi_sys::Color)"),
            "const-ptr arg borrows: {out}"
        );
        assert!(
            out.contains("(p as *const flowi_sys::Color)"),
            "const-ptr arg casts out: {out}"
        );
    }

    // An optional-pointer return (`*const T?` / `*T?`) would spell `Option<&'a T>` with
    // an unconstrained 'a no façade parameter carries - a caller could infer 'static
    // and outlive the C-owned pointee. facade_return panics instead.
    #[test]
    #[should_panic(expected = "cannot get a sound safe façade")]
    fn facade_rejects_optional_pointer_return() {
        let def = parse_one(
            "api Painter {\n\
                 probe() -> *const Color?\n\
             }",
            "painter.def",
        );
        let probe = def.apis[0]
            .functions
            .iter()
            .find(|f| f.name == "probe")
            .unwrap();
        let mut buf = Vec::new();
        RustGen::generate_facade_fn(&mut buf, probe).unwrap();
    }

    /// A `[status]` slot maps to `Result<T, crate::FlError>` in the direct-link façade:
    /// the integer status return decodes through crate::FlError::from_status, and a
    /// trailing `*mut T` out-param becomes the Ok value (dropped from the signature)
    /// while a status-only slot yields `Result<(), crate::FlError>`.
    #[test]
    fn facade_status_slot_maps_to_result() {
        let def = parse_one(
            "api Store {\n\
                 [status] parse(base: u64, out: *u64) -> i32\n\
                 [status] flush() -> i32\n\
             }",
            "store.def",
        );
        let store = def.apis.iter().find(|a| a.name == "Store").unwrap();
        let mut buf = Vec::new();
        for func in store
            .functions
            .iter()
            .filter(|f| RustGen::facade_generates(f))
        {
            RustGen::generate_facade_fn(&mut buf, func).unwrap();
        }
        let out = String::from_utf8(buf).unwrap();

        assert!(
            out.contains("pub fn parse(base: u64) -> Result<u64, crate::FlError>"),
            "out-param status signature: {out}"
        );
        assert!(
            out.contains("let mut out = core::mem::MaybeUninit::<u64>::uninit();"),
            "out-param MaybeUninit: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_store_parse(base, out.as_mut_ptr())"),
            "out-param crosses as as_mut_ptr: {out}"
        );
        assert!(
            out.contains("crate::FlError::from_status(status)?;")
                && out.contains("Ok(unsafe { out.assume_init() })"),
            "status decode + Ok lift: {out}"
        );

        assert!(
            out.contains("pub fn flush() -> Result<(), crate::FlError>"),
            "status-only signature: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_store_flush()") && out.contains("Ok(())"),
            "status-only call + Ok(()): {out}"
        );
    }

    /// A `[borrowed]` slot lowers its String args to flowi_sys::RawStr::borrow
    /// instead of the default per-frame-arena copy, and a String return lifts the C
    /// FlString view into an owned String via RawStr::into_string. An unmarked
    /// sibling slot keeps the arena copy; both façade paths apply the marker.
    #[test]
    fn borrowed_string_arg_and_string_return_lowering() {
        let def = parse_one(
            "#[handle(u32, invalid = 0)]\nstruct FontId {}\n\
             api Font {\n\
                 [borrowed] load(path: String, default_size: u16) -> FontId\n\
                 unmarked(label: String)\n\
             }\n\
             api TextInput {\n\
                 [drop] destroy(state: *void)\n\
                 [borrowed] set_text(state: *void, text: String)\n\
                 [const] [rename(text)] get_text(state: *void) -> String\n\
             }",
            "font.def",
        );

        let font = def
            .apis
            .iter()
            .find(|a| a.name == "Font")
            .expect("Font block");
        let mut fbuf = Vec::new();
        for func in font
            .functions
            .iter()
            .filter(|f| RustGen::facade_generates(f))
        {
            RustGen::generate_facade_fn(&mut fbuf, func).unwrap();
        }
        let fout = String::from_utf8(fbuf).unwrap();
        assert!(
            fout.contains(
                "flowi_sys::fl_font_load(flowi_sys::RawStr::borrow(path.as_ref()), default_size)"
            ),
            "borrowed slot lowers via RawStr::borrow: {fout}"
        );
        assert!(
            fout.contains("{ let s = label.as_ref(); flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()) }"),
            "unmarked slot keeps arena copy: {fout}"
        );

        // RAII receiver slots (api TextInput): state is threaded as self.handle.
        let ti = def
            .apis
            .iter()
            .find(|a| a.name == "TextInput")
            .expect("TextInput block");
        let drop_fn = RustGen::api_drop_fn(ti).expect("drop slot");
        let handle = RustGen::raii_handle_name(drop_fn);
        let mut tbuf = Vec::new();
        for func in ti.functions.iter().filter(|f| {
            RustGen::raii_generates(f) && f.function_args.iter().any(|a| a.name == handle)
        }) {
            RustGen::generate_raii_method(&mut tbuf, func, handle).unwrap();
        }
        let tout = String::from_utf8(tbuf).unwrap();
        assert!(
            tout.contains("pub fn set_text(&mut self, text: impl AsRef<str>)"),
            "set_text receiver + arg: {tout}"
        );
        assert!(
            tout.contains("flowi_sys::fl_text_input_set_text(self.handle, flowi_sys::RawStr::borrow(text.as_ref()))"),
            "set_text borrows + threads handle: {tout}"
        );
        assert!(
            tout.contains("pub fn text(&self) -> String"),
            "get_text renamed to text, &self, String return: {tout}"
        );
        assert!(
            tout.contains(
                "let ret = flowi_sys::fl_text_input_get_text(self.handle); ret.into_string()"
            ),
            "String return lifted via into_string: {tout}"
        );
    }

    /// A `[slice(T)]` / `[slice_mut(T)]` arg folds its (pointer, count) pair into one
    /// `&[T]` / `&mut [T]` façade param - the data pointer crosses as
    /// as_ptr()/as_mut_ptr() and the immediately-following count arg leaves the
    /// façade, crossing as `len() as <count-width>`. An unmarked sibling pointer arg
    /// keeps its &mut T lowering.
    #[test]
    fn slice_and_slice_mut_arg_lowering() {
        let def = parse_one(
            "api SelectionSet {\n\
                 [drop] destroy(set: *void)\n\
                 set_all(set: *void, [slice(u64)] ids: *void, count: u64)\n\
                 [const] copy_ids(set: *void, [slice_mut(u64)] out: *void, cap: u64) -> u64\n\
                 raw(set: *void, other: *u32)\n\
             }\n\
             api UiList {\n\
                 begin(id: u32, [slice(u64)] ordered_ids: *void, count: u32)\n\
             }",
            "ui_selection.def",
        );

        let ui_list = def
            .apis
            .iter()
            .find(|a| a.name == "UiList")
            .expect("UiList block");
        let mut sbuf = Vec::new();
        for func in ui_list
            .functions
            .iter()
            .filter(|f| RustGen::facade_generates(f))
        {
            RustGen::generate_facade_fn(&mut sbuf, func).unwrap();
        }
        let sout = String::from_utf8(sbuf).unwrap();
        assert!(
            sout.contains("pub fn begin(id: u32, ordered_ids: &[u64])"),
            "stateless slice param collapses ptr+count: {sout}"
        );
        assert!(
            sout.contains("fl_ui_list_begin(id, ordered_ids.as_ptr() as *mut core::ffi::c_void, ordered_ids.len() as u32)"),
            "stateless slice crosses as ptr + len cast to the u32 count width: {sout}"
        );

        let api = def
            .apis
            .iter()
            .find(|a| a.name == "SelectionSet")
            .expect("block");
        let drop_fn = RustGen::api_drop_fn(api).expect("drop slot");
        let handle = RustGen::raii_handle_name(drop_fn);
        let mut buf = Vec::new();
        for func in api.functions.iter().filter(|f| {
            RustGen::raii_generates(f) && f.function_args.iter().any(|a| a.name == handle)
        }) {
            RustGen::generate_raii_method(&mut buf, func, handle).unwrap();
        }
        let out = String::from_utf8(buf).unwrap();

        assert!(
            out.contains("pub fn set_all(&mut self, ids: &[u64])"),
            "slice param collapses ptr+count: {out}"
        );
        assert!(
            out.contains("fl_selection_set_set_all(self.handle, ids.as_ptr() as *mut core::ffi::c_void, ids.len() as u64)"),
            "slice crosses as ptr + len: {out}"
        );
        assert!(
            out.contains("pub fn copy_ids(&self, out: &mut [u64]) -> u64"),
            "slice_mut param is &mut [T] on &self: {out}"
        );
        assert!(
            out.contains("fl_selection_set_copy_ids(self.handle, out.as_mut_ptr() as *mut core::ffi::c_void, out.len() as u64)"),
            "slice_mut crosses as mut ptr + len: {out}"
        );
        assert!(
            out.contains("pub fn raw(&mut self, other: &mut u32)"),
            "unmarked pointer arg unaffected: {out}"
        );
    }

    /// A `[*const String]` array arg takes `&[impl AsRef<str>]` on the safe surface and
    /// packs the RawStr array the ABI wants at the call site, each element copied into
    /// the per-frame arena. A struct element (PolyPoint) is unaffected.
    #[test]
    fn string_array_arg_takes_str_slice_and_packs_raw_str() {
        let def = parse_one(
            "struct Cfg { a: i32 }\n\
             api Tabs { new_impl(tabs: [*const String], config: Cfg) -> bool\n\
                        pts(points: [*const PolyPoint]) }",
            "tabs.def",
        );
        let api = def
            .apis
            .iter()
            .find(|a| a.name == "Tabs")
            .expect("Tabs block");
        let mut buf = Vec::new();
        for func in api
            .functions
            .iter()
            .filter(|f| RustGen::facade_generates(f))
        {
            RustGen::generate_facade_fn(&mut buf, func).unwrap();
        }
        let out = String::from_utf8(buf).unwrap();
        assert!(
            out.contains("tabs: &[impl AsRef<str>]"),
            "String array takes a slice of ergonomic strings: {out}"
        );
        assert!(
            !out.contains("&[flowi_sys::RawStr]"),
            "the raw RawStr mirror never reaches a safe signature: {out}"
        );
        assert!(
            out.contains("let tabs_frame = flowi_sys::fl_frame_str_array(tabs.len() as u32);"),
            "the mirror array is reserved from the frame arena: {out}"
        );
        assert!(
            out.contains("*tabs_frame.add(i) = flowi_sys::fl_frame_str("),
            "each string is copied into the reserved frame-arena slot: {out}"
        );
        assert!(
            !out.contains("Vec<"),
            "no heap allocation is introduced for the packed array: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_tabs_impl(tabs_frame, tabs.len() as u32"),
            "String array crosses as the arena pointer + len: {out}"
        );
        assert!(
            out.contains("points: &[flowi_sys::PolyPoint]"),
            "struct array element is unchanged: {out}"
        );
    }

    /// A mutable string array (`[*String]`) has no sound safe lowering - a RawStr
    /// out-array cannot be read back from safe code - so generation fails rather than
    /// emit an unusable signature.
    #[test]
    fn mutable_string_array_arg_is_rejected() {
        let def = parse_one("api Tabs { fill_impl(tabs: [*String]) }", "tabs.def");
        let api = def
            .apis
            .iter()
            .find(|a| a.name == "Tabs")
            .expect("Tabs block");
        let err = RustGen::lower_loose_symbol_args(
            LooseSymbolSurface::DirectLink,
            &api.functions[0],
            None,
            None,
        )
        .expect_err("mutable string array must be rejected");
        assert!(
            err.contains("mutable string array"),
            "diagnostic names the rejected shape: {err}"
        );
    }

    /// An api block with a `[drop]` slot emits an RAII opaque-handle façade - a
    /// pub(crate) handle-owning struct, an impl Drop calling the `[drop]`
    /// destructor on a non-null handle, and receiver methods threading self.handle in
    /// the handle argument's position, which may be other than first (show(label,
    /// state)). `[const]` -> &self, default -> &mut self, `[rename(x)]` overrides
    /// the name; the constructor and `[manual]` slots are left hand-written.
    #[test]
    fn raii_drop_block_emits_handle_struct_drop_and_receiver_methods() {
        let api_def = parse_one(
            "api Widget {\n\
                 [manual] create(capacity: u32) -> *void\n\
                 [drop] destroy(state: *void)\n\
                 clear(state: *void)\n\
                 [const] peek(state: *void, id: u64) -> bool\n\
                 [rename(show)] show(label: String, state: *void) -> Signal\n\
                 [manual] get_text(state: *void) -> String\n\
             }",
            "widget.def",
        );
        let api = &api_def.apis[0];
        let drop_fn = RustGen::api_drop_fn(api).expect("drop fn");
        let mut buf = Vec::new();
        RustGen::generate_raii_facade(&mut buf, api, drop_fn).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("pub struct Widget {\n    pub(crate) handle: *mut core::ffi::c_void,\n}"),
            "handle-owning struct: {out}"
        );
        assert!(out.contains("impl Drop for Widget {"), "Drop impl: {out}");
        assert!(
            out.contains("unsafe { flowi_sys::fl_widget_destroy(self.handle) };"),
            "Drop calls [drop]: {out}"
        );
        assert!(
            out.contains("self.handle = core::ptr::null_mut();"),
            "Drop nulls the handle: {out}"
        );
        assert!(
            out.contains("pub fn clear(&mut self) {"),
            "default &mut self receiver: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_widget_clear(self.handle)"),
            "handle threaded: {out}"
        );
        assert!(
            out.contains("pub fn peek(&self, id: u64) -> bool {"),
            "[const] -> &self: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_widget_peek(self.handle, id)"),
            "handle + passthrough arg: {out}"
        );
        assert!(
            out.contains("pub fn show(&mut self, label: impl AsRef<str>) -> flowi_sys::Signal {"),
            "string arg method: {out}"
        );
        assert!(
            out.contains(
                "flowi_sys::fl_widget_show({ let s = label.as_ref(); flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()) }, self.handle)"
            ),
            "handle threaded in 2nd position: {out}"
        );
        assert!(
            !out.contains("fn create"),
            "constructor stays hand-written: {out}"
        );
        assert!(
            !out.contains("fn get_text"),
            "[manual] slot stays hand-written: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("raii facade compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "#![allow(improper_ctypes)]\n\
             pub mod flowi_sys {{\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct Signal {{ pub clicked: bool }}\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct RawStr {{ pub data: *const core::ffi::c_char, pub packed: u64 }}\n\
                extern \"C\" {{\n\
                    pub fn fl_frame_str(ptr: *const core::ffi::c_char, len: usize) -> RawStr;\n\
                    pub fn fl_widget_destroy(h: *mut core::ffi::c_void);\n\
                    pub fn fl_widget_clear(h: *mut core::ffi::c_void);\n\
                    pub fn fl_widget_peek(h: *mut core::ffi::c_void, id: u64) -> bool;\n\
                    pub fn fl_widget_show(label: RawStr, h: *mut core::ffi::c_void) -> Signal;\n\
                }}\n\
             }}\n\
             {out}",
            out = out,
        );
        assert!(
            rustc_compiles(rustc, "raii_facade", &src),
            "the generated RAII façade must compile"
        );
    }

    /// An RAII `[drop]` whose handle is a typed opaque pointer (`*App`, not `*void`)
    /// owns it as `*mut flowi_sys::App`, and Drop + the receiver slots thread
    /// self.handle straight into the `fl_app_*` slots that take that exact pointer,
    /// no cast.
    #[test]
    fn raii_typed_opaque_handle_owns_typed_pointer() {
        let api_def = parse_one(
            "#[module(app)]\n\
             #[attributes(Opaque)]\n\
             struct App {}\n\
             api App {\n\
                 [manual] create(settings: *const u32) -> *App\n\
                 [drop] destroy(app: *App)\n\
                 set_ui_zoom(app: *App, zoom: f32)\n\
                 [const] headless_relative_mouse_mode(app: *App) -> bool\n\
             }",
            "app.def",
        );
        let api = api_def
            .apis
            .iter()
            .find(|a| a.name == "App")
            .expect("api block");
        let drop_fn = RustGen::api_drop_fn(api).expect("drop fn");
        let mut buf = Vec::new();
        RustGen::generate_raii_facade(&mut buf, api, drop_fn).expect("emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("pub struct App {\n    pub(crate) handle: *mut flowi_sys::App,\n}"),
            "typed handle field: {out}"
        );
        assert!(
            out.contains("unsafe { flowi_sys::fl_app_destroy(self.handle) };"),
            "Drop calls [drop]: {out}"
        );
        assert!(
            out.contains("pub fn set_ui_zoom(&mut self, zoom: f32) {"),
            "default &mut self: {out}"
        );
        assert!(
            out.contains("flowi_sys::fl_app_set_ui_zoom(self.handle, zoom)"),
            "handle threaded: {out}"
        );
        assert!(
            out.contains("pub fn headless_relative_mouse_mode(&self) -> bool {"),
            "[const] -> &self: {out}"
        );
        assert!(
            !out.contains("fn create"),
            "constructor stays hand-written: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("typed-handle raii facade compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "pub mod flowi_sys {{\n\
                pub enum App {{}}\n\
                extern \"C\" {{\n\
                    pub fn fl_app_destroy(app: *mut App);\n\
                    pub fn fl_app_set_ui_zoom(app: *mut App, zoom: f32);\n\
                    pub fn fl_app_headless_relative_mouse_mode(app: *mut App) -> bool;\n\
                }}\n\
             }}\n\
             {out}",
            out = out,
        );
        assert!(
            rustc_compiles(rustc, "raii_typed_handle", &src),
            "the typed-handle RAII façade must compile"
        );
    }

    /// An api block with a `[scope_begin]` / `[scope_end]` pair emits a scope-guard
    /// façade - a zero-sized `#[must_use]` `<Domain>Scope` token whose Drop runs the
    /// paired end slot, a begin method returning that guard, and an end method that
    /// consumes the guard by value, so a double close is a compile error.
    #[test]
    fn scope_begin_end_pair_emits_guard_struct_and_begin_returns_it() {
        let api_def = parse_one(
            "api Popup {\n\
                 [scope_begin] begin(anchor_id: LayoutId, config: PopupConfig)\n\
                 [scope_end] end()\n\
                 tooltip(anchor_id: LayoutId, text: String)\n\
                 [manual] message_box(open: *bool) -> DialogResult\n\
             }",
            "popup.def",
        );
        // generate_facade writes a file; reproduce the stateless+scope branch into a
        // buffer so the test needs no temp dir.
        let api = &api_def.apis[0];
        let mut buf = Vec::new();
        let begin_fn = RustGen::api_scope_begin_fn(api).expect("scope_begin slot");
        let end_fn = RustGen::api_scope_end_fn(api).expect("scope_end slot");
        RustGen::generate_scope_guard(&mut buf, api, begin_fn, end_fn).expect("guard");
        let guard = RustGen::scope_guard_name(api);
        writeln!(buf, "pub struct {};", api.name).unwrap();
        writeln!(buf, "impl {} {{", api.name).unwrap();
        for func in api
            .functions
            .iter()
            .filter(|f| RustGen::facade_generates(f))
        {
            if func.is_scope_begin {
                RustGen::generate_scope_begin_fn(&mut buf, func, &guard).unwrap();
            } else if func.is_scope_end {
                RustGen::generate_scope_end_fn(&mut buf, func, &guard).unwrap();
            } else {
                RustGen::generate_facade_fn(&mut buf, func).unwrap();
            }
        }
        writeln!(buf, "}}").unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("#[must_use ="), "guard is must_use: {out}");
        assert!(
            out.contains("pub struct PopupScope {\n    // Zero-sized token:"),
            "guard struct named <Domain>Scope: {out}"
        );
        assert!(
            out.contains("    _priv: (),"),
            "zero-sized private token: {out}"
        );
        assert!(
            out.contains("impl Drop for PopupScope {"),
            "Drop impl: {out}"
        );
        assert!(
            out.contains("unsafe { flowi_sys::fl_popup_end() };"),
            "Drop runs the end slot: {out}"
        );
        assert!(
            out.contains("pub fn begin(anchor_id: impl Into<crate::LayoutId>, config: flowi_sys::PopupConfig) -> PopupScope {"),
            "begin returns the guard: {out}"
        );
        assert!(
            out.contains(
                "unsafe { flowi_sys::fl_popup_begin(anchor_id.into().into_sys(), config) };"
            ),
            "begin forwards: {out}"
        );
        assert!(
            out.contains("PopupScope { _priv: () }"),
            "begin hands back the guard: {out}"
        );
        assert!(
            out.contains("pub fn end(scope: PopupScope) {"),
            "end consumes the guard: {out}"
        );
        assert!(
            out.contains("core::mem::forget(scope);"),
            "end mem::forgets the guard so Drop does not double-close: {out}"
        );
        assert!(
            out.contains(
                "pub fn tooltip(anchor_id: impl Into<crate::LayoutId>, text: impl AsRef<str>)"
            ),
            "non-scope slot generates: {out}"
        );
        assert!(
            !out.contains("fn message_box"),
            "manual slot skipped: {out}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("scope-guard facade compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "pub struct LayoutId(pub u64);\n\
             impl From<&str> for LayoutId {{ fn from(_: &str) -> Self {{ LayoutId(0) }} }}\n\
             impl LayoutId {{ fn into_sys(self) -> u64 {{ self.0 }} }}\n\
             pub mod flowi_sys {{\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct PopupConfig {{ pub z: i16 }}\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct TooltipConfig {{ pub z: i16 }}\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct RawStr {{ pub data: *const core::ffi::c_char, pub packed: u64 }}\n\
                extern \"C\" {{\n\
                    pub fn fl_frame_str(ptr: *const core::ffi::c_char, len: usize) -> RawStr;\n\
                    pub fn fl_popup_begin(anchor_id: u64, config: PopupConfig);\n\
                    pub fn fl_popup_end();\n\
                    pub fn fl_popup_tooltip(anchor_id: u64, text: RawStr);\n\
                }}\n\
             }}\n\
             {out}\n\
             // Exercise the protocol: begin returns the guard, end consumes it - closing exactly once.\n\
             fn _use_scope() {{ let s = Popup::begin(\"x\", flowi_sys::PopupConfig {{ z: 0 }}); Popup::end(s); }}\n",
            out = out,
        );
        assert!(
            rustc_compiles(rustc, "scope_facade", &src),
            "the generated scope-guard façade must compile"
        );

        // Consuming the guard turns a double close into E0382 use-after-move rather
        // than a runtime double end. Reuse the façade proven to compile above, then
        // append a slot that closes the same guard twice; it must be rejected.
        let double_close = format!(
            "{src}\n\
             fn _double_close() {{ let s = Popup::begin(\"x\", flowi_sys::PopupConfig {{ z: 0 }}); Popup::end(s); Popup::end(s); }}\n",
            src = src,
        );
        assert!(
            !rustc_compiles(rustc, "scope_double_close", &double_close),
            "closing a consumed scope guard twice must be a compile error, not a runtime double end"
        );
    }

    // ================= service-consume wrapper =================

    /// Parse an inline def under a specific naming profile (the default [`parse_one`]
    /// uses FL), so a test can prove the Rust wrapper is prefix-free across profiles.
    fn parse_named(defs: &str, file: &str, naming: &crate::naming::Naming) -> ApiDef {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(defs, file, &mut api_def);
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), naming);
        api_def
    }

    /// A representative annotated service used by several wrapper tests.
    const GADGET_DEF: &str = "struct Widget {}\n\
         #[attributes(service, thread_safe)]\n\
         api Gadget {\n\
             [transfer(free = widget_free)] widget_new(size: u64) -> *Widget\n\
             widget_free([transfer] w: *Widget)\n\
             consume([transfer] w: *Widget)\n\
             poke(w: *const Widget, value: u32)\n\
             [retained] watch(cfg: *const Widget)\n\
             [status] parse(base: u64, out: *u64) -> i32\n\
             [status] flush() -> i32\n\
             try_peek(key: u64, out: *u32) -> bool\n\
             equals(a: u64, b: u64) -> bool\n\
             reset()\n\
             depth() -> u32\n\
             [manual] custom(x: u32)\n\
         }";

    /// The two loose-symbol consumers are projections of one lowering model: this
    /// matrix pins the shared semantic shapes and the few intentional storage-policy
    /// differences.
    #[test]
    fn loose_symbol_lowering_matrix_covers_both_consumers() {
        let def = parse_one(
            "struct Widget {}\n\
             api Gadget {\n\
                 [transfer(free = free)] make() -> *Widget\n\
                 free([transfer] w: *Widget)\n\
                 consume([transfer] w: *Widget)\n\
                 [status] parse(base: u64, out: *u64) -> i32\n\
                 try_peek(key: u64, out: *u32) -> bool\n\
                 [retained] watch(cfg: *const Widget)\n\
                 [borrowed] label(text: String) -> String\n\
             }",
            "gadget.def",
        );
        let api = &def.apis[0];
        let function = |name: &str| api.functions.iter().find(|f| f.name == name).unwrap();
        let direct = LooseSymbolSurface::DirectLink;
        let external = LooseSymbolSurface::ExternalConsumer;

        for surface in [direct, external] {
            assert_eq!(
                RustGen::lower_loose_symbol_result(surface, function("parse")).unwrap(),
                LoweredResult::Status {
                    ok_ty: "u64".to_owned(),
                    has_out: true,
                }
            );
            assert_eq!(
                RustGen::lower_loose_symbol_result(surface, function("make")).unwrap(),
                LoweredResult::Transfer {
                    owned_ty: "OwnedWidget".to_owned(),
                }
            );
            assert_eq!(
                RustGen::lower_loose_symbol_result(surface, function("try_peek")).unwrap(),
                LoweredResult::Option {
                    ty: "u32".to_owned(),
                }
            );
            let consume =
                RustGen::lower_loose_symbol_args(surface, function("consume"), None, None).unwrap();
            assert_eq!(consume.params, ["w: OwnedWidget"]);
            assert_eq!(consume.prelude, ["let w_ptr = w.into_raw();"]);
        }

        let direct_retained =
            RustGen::lower_loose_symbol_args(direct, function("watch"), None, None).unwrap();
        let external_retained =
            RustGen::lower_loose_symbol_args(external, function("watch"), None, None).unwrap();
        assert_eq!(direct_retained.params, ["cfg: &flowi_sys::Widget"]);
        assert!(!direct_retained.prelude.is_empty());
        assert_eq!(external_retained.params, ["cfg: &'static crate::Widget"]);
        assert!(external_retained.prelude.is_empty());

        let direct_string =
            RustGen::lower_loose_symbol_args(direct, function("label"), None, None).unwrap();
        let external_string =
            RustGen::lower_loose_symbol_args(external, function("label"), None, None).unwrap();
        assert_eq!(direct_string.params, external_string.params);
        assert_eq!(
            direct_string.ffi,
            ["flowi_sys::RawStr::borrow(text.as_ref())"]
        );
        assert_eq!(
            external_string.ffi,
            ["crate::RawStr::borrow(text.as_ref())"]
        );
        // A `[borrowed]` String return splits by surface: the service wrapper's &self
        // anchors a view, the stateless façade has nothing to anchor it to and copies.
        assert!(matches!(
            RustGen::lower_loose_symbol_result(external, function("label")).unwrap(),
            LoweredResult::Value { ty, .. } if ty == "&str"
        ));
        assert!(matches!(
            RustGen::lower_loose_symbol_result(direct, function("label")).unwrap(),
            LoweredResult::Value { ty, .. } if ty == "String"
        ));
    }

    #[test]
    fn direct_facade_emits_usable_option_and_transfer_surface() {
        let def = parse_one(
            "struct Widget {}\n\
             api Gadget {\n\
                 [transfer(free = free)] make() -> *Widget\n\
                 free([transfer] w: *Widget)\n\
                 consume([transfer] w: *Widget)\n\
                 try_peek(key: u64, out: *u32) -> bool\n\
             }",
            "gadget.def",
        );
        let dir = std::env::temp_dir().join(format!("api_gen_direct_loose_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create façade dir");
        assert!(
            RustGen::generate_facade(dir.to_str().unwrap(), &def, "scripts/gen.sh")
                .expect("generate façade")
        );
        let out = std::fs::read_to_string(dir.join("gadget.rs")).expect("read façade");
        let _ = std::fs::remove_dir_all(&dir);

        assert!(out.contains("pub struct OwnedWidget"), "{out}");
        assert!(out.contains("flowi_sys::fl_gadget_free(self.ptr)"), "{out}");
        assert!(
            out.contains("pub fn make() -> OwnedWidget")
                && out.contains("pub fn consume(w: OwnedWidget)"),
            "{out}"
        );
        assert!(
            !out.contains("pub fn free("),
            "paired destructor must only be called by Drop: {out}"
        );
        assert!(
            out.contains("pub fn try_peek(key: u64) -> Option<u32>"),
            "{out}"
        );

        let Some(rustc) = find_rustc() else {
            return;
        };
        let body = strip_file_header(&out);
        let src = format!(
            "#![allow(dead_code)]\n\
             mod flowi_sys {{\n\
                 pub enum Widget {{}}\n\
                 pub unsafe fn fl_gadget_make() -> *mut Widget {{ core::ptr::null_mut() }}\n\
                 pub unsafe fn fl_gadget_free(_: *mut Widget) {{}}\n\
                 pub unsafe fn fl_gadget_consume(_: *mut Widget) {{}}\n\
                 pub unsafe fn fl_gadget_try_peek(_: u64, _: *mut u32) -> bool {{ false }}\n\
             }}\n\
             {body}\n",
        );
        assert!(
            rustc_compiles(rustc, "direct_loose_surface", &src),
            "generated option/transfer façade must compile"
        );
    }

    /// FlError decodes an i32, so the status conversion is emitted only when the
    /// slot declares something else - an i32-to-i32 cast is a clippy warning.
    #[test]
    fn status_decode_casts_only_a_non_i32_status() {
        let i32_status = parse_one("api Store { [status] flush() -> i32 }", "store_i32.def");
        let mut buf: Vec<u8> = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &i32_status.apis[0].functions[0]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(
            out.contains("from_status(status)?;") && !out.contains("status as i32"),
            "{out}"
        );

        let wide_status = parse_one("api Store { [status] flush() -> i64 }", "store_i64.def");
        let mut buf: Vec<u8> = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &wide_status.apis[0].functions[0]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("from_status(status as i32)?;"), "{out}");
    }

    /// A forwarder past clippy's argument-count threshold carries the allow - its
    /// arity is the mirrored C prototype's, not a codegen choice. Nesting in a
    /// parameter type does not inflate the count.
    #[test]
    fn wide_forwarders_allow_the_argument_count_lint() {
        assert_eq!(RustGen::param_count(""), 0);
        assert_eq!(RustGen::param_count("a: u32"), 1);
        assert_eq!(
            RustGen::param_count("a: Option<&'a T>, cb: extern \"C\" fn(u32) -> bool, c: u8"),
            3
        );

        let def = parse_one(
            "api Painter {\n\
                 wide(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, h: f32)\n\
                 narrow(a: f32)\n\
             }",
            "painter_arity.def",
        );
        let mut buf: Vec<u8> = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &def.apis[0].functions[0]).unwrap();
        assert!(String::from_utf8(buf)
            .unwrap()
            .contains("#[allow(clippy::too_many_arguments)]"));
        let mut buf: Vec<u8> = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &def.apis[0].functions[1]).unwrap();
        assert!(!String::from_utf8(buf)
            .unwrap()
            .contains("too_many_arguments"));
    }

    /// A generated file that forwards through unsafe carries the shared //! SAFETY:
    /// statement and the allow that makes it satisfy undocumented_unsafe_blocks;
    /// a file of pure type bindings carries neither.
    #[test]
    fn generated_files_document_unsafe_only_where_it_appears() {
        let forwarding = RustGen::generated_header(
            "    unsafe { fl_cursor_set_visible(v) }\n",
            "scripts/gen.sh",
        );
        assert!(
            forwarding.contains("//! SAFETY:")
                && forwarding.contains("#![allow(clippy::undocumented_unsafe_blocks)]"),
            "{forwarding}"
        );
        let bindings =
            RustGen::generated_header("pub struct Rect { pub x: f32 }\n", "scripts/gen.sh");
        assert!(
            !bindings.contains("SAFETY") && !bindings.contains("#!["),
            "{bindings}"
        );
        assert!(bindings.starts_with("// @generated"), "{bindings}");
    }

    /// The shared safety statement lands above the first item.
    #[test]
    fn facade_file_leads_with_the_shared_safety_statement() {
        let def = parse_one("api Cursor { set_visible(visible: bool) }", "cursor.def");
        let dir = std::env::temp_dir().join(format!("api_gen_safety_hdr_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create façade dir");
        assert!(
            RustGen::generate_facade(dir.to_str().unwrap(), &def, "scripts/gen.sh")
                .expect("generate façade")
        );
        let out = std::fs::read_to_string(dir.join("cursor.rs")).expect("read façade");
        let _ = std::fs::remove_dir_all(&dir);

        let safety = out.find("//! SAFETY:").expect(&out);
        let allow = out
            .find("#![allow(clippy::undocumented_unsafe_blocks)]")
            .expect(&out);
        let first_item = out.find("pub struct Cursor").expect(&out);
        assert!(safety < allow && allow < first_item, "{out}");
    }

    #[test]
    fn raii_facade_uses_shared_status_option_and_transfer_lowering() {
        let def = parse_one(
            "struct Widget {}\n\
             api Store {\n\
                 [drop] destroy(state: *void)\n\
                 [status] parse(state: *void, key: u64, out: *u64) -> i32\n\
                 peek(state: *void, key: u64, out: *u32) -> bool\n\
                 [transfer(free = free)] make(state: *void) -> *Widget\n\
                 free([transfer] w: *Widget)\n\
                 consume(state: *void, [transfer] w: *Widget)\n\
             }",
            "store.def",
        );
        let dir = std::env::temp_dir().join(format!("api_gen_raii_loose_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create façade dir");
        assert!(
            RustGen::generate_facade(dir.to_str().unwrap(), &def, "scripts/gen.sh")
                .expect("generate façade")
        );
        let out = std::fs::read_to_string(dir.join("store.rs")).expect("read façade");
        let _ = std::fs::remove_dir_all(&dir);

        assert!(
            out.contains("pub fn parse(&mut self, key: u64) -> Result<u64, crate::FlError>"),
            "{out}"
        );
        assert!(
            out.contains("pub fn peek(&mut self, key: u64) -> Option<u32>"),
            "{out}"
        );
        assert!(
            out.contains("pub fn make(&mut self) -> OwnedWidget"),
            "{out}"
        );
        assert!(
            out.contains("pub fn consume(&mut self, w: OwnedWidget)"),
            "{out}"
        );
        assert!(!out.contains("pub fn free("), "{out}");
    }

    /// A service def emits a wrapper module - the exported-symbol extern "C" block
    /// plus a forwarding wrapper - with every ownership annotation lowered.
    #[test]
    fn service_wrapper_emits_module_and_all_behaviors() {
        let def = parse_one(GADGET_DEF, "gadget.def");
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .expect("classifies")
                .expect("a service def emits a module");

        // A `[manual]` slot keeps its symbol declaration - a hand-written adapter calls
        // it - and just gets no wrapper method.
        assert!(out.contains("extern \"C\" {"), "{out}");
        assert!(
            !out.contains("pub struct GadgetApi {")
                && !out.contains("pub private_data")
                && !out.contains("Option<unsafe extern \"C\" fn"),
            "no vtable ABI mirror is emitted: {out}"
        );
        assert!(
            out.contains("pub fn custom(x: u32);"),
            "a [manual] slot still exports its symbol declaration: {out}"
        );

        assert!(
            out.contains("pub struct Gadget {\n    _marker: PhantomData<*const ()>,\n}"),
            "{out}"
        );
        assert!(out.contains("pub const fn new() -> Self {"), "{out}");
        assert!(!out.contains("from_vtable"), "no vtable constructor: {out}");

        assert!(
            out.contains("pub fn poke(&self, w: &crate::Widget, value: u32) {")
                && out.contains("poke(w as *const crate::Widget, value)"),
            "unannotated borrow-for-call lowering: {out}"
        );
        // A bool with no out-param stays a plain bool, NOT an Option.
        assert!(out.contains("pub fn depth(&self) -> u32 {"), "{out}");
        assert!(
            out.contains("pub fn equals(&self, a: u64, b: u64) -> bool {"),
            "plain bool: {out}"
        );

        assert!(
            out.contains("pub fn watch(&self, cfg: &'static crate::Widget) {"),
            "[retained] -> &'static: {out}"
        );

        assert!(
            !out.contains("pub fn custom(&self"),
            "a [manual] slot emits no wrapper method: {out}"
        );

        assert!(out.contains("unsafe impl Send for Gadget {}"), "{out}");
        assert!(out.contains("unsafe impl Sync for Gadget {}"), "{out}");
    }

    /// `[transfer]` - an owning `Owned<T>` newtype whose Drop calls the paired
    /// destroy slot, the destroy slot excluded from the wrapper's methods, and a
    /// `[transfer]` param moving that newtype back across the ABI.
    #[test]
    fn service_wrapper_transfer_ownership() {
        let def = parse_one(GADGET_DEF, "gadget.def");
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();

        assert!(
            out.contains("pub struct OwnedWidget {\n    ptr: *mut crate::Widget,\n}"),
            "{out}"
        );
        assert!(
            out.contains("impl Drop for OwnedWidget {") && out.contains("widget_free(self.ptr)"),
            "Drop returns the pointer via the paired destroy symbol: {out}"
        );
        assert!(out.contains("pub fn into_raw(self)"), "{out}");

        assert!(
            out.contains("pub fn widget_new(&self, size: u64) -> OwnedWidget {")
                && out.contains("OwnedWidget { ptr }"),
            "{out}"
        );
        // The destroy slot is reached only through Drop; its symbol is still declared
        // in the extern block for Drop to call.
        assert!(
            !out.contains("pub fn widget_free(&self"),
            "destroy slot has no wrapper method: {out}"
        );
        assert!(
            out.contains("pub fn consume(&self, w: OwnedWidget) {")
                && out.contains("let w_ptr = w.into_raw();")
                && out.contains("consume(w_ptr)"),
            "[transfer] param moves by value: {out}"
        );
    }

    /// `[status]` -> `Result<T, FlError>` (trailing out-param = Ok value, or () when
    /// status-only); a bool + out-param (no `[status]`) -> `Option<T>`.
    #[test]
    fn service_wrapper_status_and_option() {
        let def = parse_one(GADGET_DEF, "gadget.def");
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();

        assert!(
            out.contains("pub fn parse(&self, base: u64) -> Result<u64, crate::FlError> {")
                && out.contains("let mut out = core::mem::MaybeUninit::<u64>::uninit();")
                && out.contains("crate::FlError::from_status(status)?;")
                && out.contains("Ok(unsafe { out.assume_init() })"),
            "[status] with out-param -> Result<T, FlError>: {out}"
        );
        assert!(
            out.contains("pub fn flush(&self) -> Result<(), crate::FlError> {")
                && out.contains("Ok(())"),
            "status-only slot -> Result<(), FlError>: {out}"
        );
        assert!(
            out.contains("pub fn try_peek(&self, key: u64) -> Option<u32> {")
                && out.contains("Some(unsafe { out.assume_init() })")
                && out.contains("None"),
            "bool + out-param -> Option<T>: {out}"
        );
    }

    /// --naming profiles produce prefix-free Rust: the wrapper is byte-identical
    /// under Fl,fl and Rp,rp.
    #[test]
    fn service_wrapper_naming_prefix_free() {
        let rp_naming = crate::naming::Naming::new("Rp", "rp");
        let fl = RustGen::build_service_wrapper(
            &parse_named(GADGET_DEF, "gadget.def", &crate::naming::FL),
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        let rp = RustGen::build_service_wrapper(
            &parse_named(GADGET_DEF, "gadget.def", &rp_naming),
            &rp_naming,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();

        assert_eq!(
            fl, rp,
            "the Rust wrapper is identical across naming profiles"
        );
        assert!(
            fl.contains("pub struct Gadget {"),
            "prefix-free domain type: {fl}"
        );
        assert!(!fl.contains("FlGadget") && !fl.contains("RpGadget"), "{fl}");
    }

    /// A service slot's name is its exported C symbol, so a profile whose exports
    /// are namespaced bakes the function prefix into the slot too. The method name
    /// peels both that prefix and the domain, so a consumer reads
    /// Metadata::get_waveform_image rather than rp_metadata_get_waveform_image.
    #[test]
    fn service_method_name_strips_the_profile_prefix_and_the_domain() {
        let rp = crate::naming::Naming::new("Rp", "rp");
        assert_eq!(
            RustGen::service_method_name(&rp, "metadata", "rp_metadata_get_waveform_image"),
            "get_waveform_image"
        );
        assert_eq!(
            RustGen::service_method_name(&rp, "content_view", "rp_content_view_begin_row"),
            "begin_row"
        );
        // flowi's own slots carry the domain but not the function prefix; the _impl
        // C body-name suffix is dropped either way.
        assert_eq!(
            RustGen::service_method_name(&crate::naming::FL, "probe", "probe_parse"),
            "parse"
        );
        assert_eq!(
            RustGen::service_method_name(&crate::naming::FL, "probe", "probe_begin_impl"),
            "begin"
        );
        assert_eq!(
            RustGen::service_method_name(&rp, "metadata", "lookup"),
            "lookup"
        );
    }

    /// Every ABI type the consume surface names is reached through crate::, never
    /// through flowi_sys - the only spelling a consumer forbidden from depending on
    /// the sys crate can compile. extern opaque deps are module-local, so they get a
    /// declaration in the module and are named unqualified.
    #[test]
    fn service_wrapper_names_abi_types_through_the_consumer_crate_root() {
        let def = parse_one(
            "extern opaque FlArena\n\
             struct Reading {}\n\
             #[attributes(service)]\n\
             api Sensor {\n\
                 read() -> Reading\n\
                 [manual] scratch(arena: *FlArena) -> Reading\n\
             }",
            "sensor.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            !out.contains("flowi_sys"),
            "the consume surface must not name the sys crate: {out}"
        );
        assert!(
            out.contains("pub fn read(&self) -> crate::Reading {"),
            "a def-authored type is reached through the crate root: {out}"
        );
        assert!(
            out.contains("pub enum FlArena {}"),
            "an `extern opaque` dep gets a module-local declaration: {out}"
        );
        assert!(
            out.contains("pub fn scratch(arena: *mut FlArena) -> crate::Reading;"),
            "the extern declaration points at that module-local type: {out}"
        );
    }

    /// With a raw bindings tree to forward through, the wrapper declares no symbols of
    /// its own: it calls through `<raw path>::<def>::<symbol>`. Two blocks declaring
    /// one symbol is duplication, and where the symbol takes an extern opaque type
    /// each block would mint its own ZST for it - the same C type under two Rust
    /// spellings, which is what clashing_extern_declarations fires on.
    #[test]
    fn service_wrapper_forwards_through_the_raw_bindings_when_given_their_path() {
        let def = parse_one(
            "extern opaque FlArena\n\
             struct Reading {}\n\
             #[attributes(service)]\n\
             api Sensor {\n\
                 read(id: u32) -> Reading\n\
                 [manual] scratch(arena: *FlArena) -> Reading\n\
             }",
            "sensor.def",
        );
        let out = RustGen::build_service_wrapper(
            &def,
            &crate::naming::FL,
            Some("crate::generated"),
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(
            !out.contains("extern \"C\""),
            "no second declaration of the same symbols: {out}"
        );
        assert!(
            !out.contains("pub enum FlArena {}"),
            "and so no second ZST for the opaque type either: {out}"
        );
        assert!(
            out.contains("unsafe { crate::generated::sensor::read(id) }"),
            "the forwarder calls through the raw module: {out}"
        );

        // Without the path the module stays self-contained.
        let standalone =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            standalone.contains("extern \"C\" {")
                && standalone.contains("pub enum FlArena {}")
                && standalone.contains("unsafe { read(id) }"),
            "{standalone}"
        );
    }

    /// An extern opaque type never reaches a generated safe signature. An out-param
    /// can slip past the parameter guard - it is consumed by the caller rather than
    /// lowered - and the `[status]` / option shapes read their buffer back through
    /// assume_init, undefined behaviour for an uninhabited type whatever C wrote. Both
    /// shapes are refused at lowering.
    #[test]
    fn opaque_out_params_are_refused() {
        for slot in [
            "[status] store_get(key: u64, out: *HostDb) -> i32",
            "store_try(key: u64, out: *HostDb) -> bool",
        ] {
            let def = parse_one(
                &format!(
                    "extern opaque HostDb\n\
                     #[attributes(service)]\n\
                     api Store {{\n    {slot}\n}}"
                ),
                "store.def",
            );
            let err = RustGen::build_service_wrapper(
                &def,
                &crate::naming::FL,
                None,
                None,
                "scripts/gen.sh",
            )
            .unwrap_err()
            .to_string();
            assert!(
                err.contains("extern opaque") && err.contains("HostDb"),
                "slot `{slot}` must be refused by name: {err}"
            );
        }
    }

    /// Peeling the prefixes off a slot can leave a bare Rust keyword, which is a method
    /// name that does not parse. The module also has to be able to name a type it
    /// returns - declared for a self-contained module, imported from the raw tree for a
    /// forwarding one, so the forwarding module never mints a second Rust type for one
    /// C type.
    #[test]
    fn keyword_verbs_still_emit_parseable_rust() {
        let def = parse_one(
            "struct HostDb { generation: u64 }\n\
             #[attributes(service)]\n\
             api Store {\n\
                 [status] store_get(key: u64, out: *HostDb) -> i32\n\
                 store_try(key: u64, out: *HostDb) -> bool\n\
                 store_depth() -> u32\n\
             }",
            "store.def",
        );

        let standalone =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            standalone.contains("pub fn r#try(&self, key: u64) -> Option<crate::HostDb> {"),
            "a slot whose verb is a keyword is escaped: {standalone}"
        );
        assert!(
            standalone
                .contains("pub fn get(&self, key: u64) -> Result<crate::HostDb, crate::FlError> {"),
            "{standalone}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("rustc not found; skipping the compile half");
            return;
        };
        let stub = "pub enum FlError { Other(i32) }\n\
             impl FlError {\n\
                 pub fn from_status(c: i32) -> Result<(), FlError> {\n\
                     if c == 0 { Ok(()) } else { Err(FlError::Other(c)) }\n\
                 }\n\
             }\n\
             #[repr(C)] pub struct HostDb { pub generation: u64 }\n";
        assert!(
            rustc_compiles(
                rustc,
                "keyword_verbs",
                &format!(
                    "#![allow(dead_code)]\n{stub}{}",
                    strip_file_header(&standalone)
                )
            ),
            "{standalone}"
        );
    }

    /// A wrapper module is a declared FFI boundary, so it carries the unsafe_code
    /// opt-out itself - a consumer crate that denies unsafe_code workspace-wide can
    /// then compile the generated tree without wrapping it. A module with no unsafe
    /// in it gets neither the opt-out nor the shared safety statement.
    #[test]
    fn service_wrapper_declares_itself_a_boundary_module() {
        let def = parse_one(
            "#[attributes(service)] api Clock { now() -> u64 }",
            "clock.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(out.contains("#![allow(unsafe_code)]"), "{out}");

        let no_unsafe = parse_one(
            "#[attributes(service)] api Clock { [manual] now() -> u64 tick() }",
            "clock.def",
        );
        let out = RustGen::build_service_wrapper(
            &no_unsafe,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(out.contains("#![allow(unsafe_code)]"), "{out}");
    }

    /// A service whose every slot is `[manual]` never gets a wrapper struct: it would be
    /// a pub handle with a new() and no method.
    ///
    /// Whether it gets a module depends on the mode, and the two are opposites. A
    /// forwarding module would hold nothing - the declarations are in the raw tree - so
    /// there is none. A self-contained module's own extern "C" block is the only
    /// declaration of those symbols anywhere, and is what the hand-written adapters
    /// call, so it must still be emitted.
    #[test]
    fn an_all_manual_service_keeps_its_declarations_but_gets_no_handle() {
        let all_manual = parse_one(
            "#[attributes(service)]\n\
             api Clock { [manual] now() -> u64 [manual] tick() }",
            "clock.def",
        );

        assert!(
            RustGen::build_service_wrapper(
                &all_manual,
                &crate::naming::FL,
                Some("crate::generated"),
                None,
                "scripts/gen.sh"
            )
            .unwrap()
            .is_none(),
            "forwarding: nothing left to put in a module"
        );

        let standalone = RustGen::build_service_wrapper(
            &all_manual,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .expect("self-contained: the declarations are only here");
        assert!(
            standalone.contains("pub fn now() -> u64;") && standalone.contains("pub fn tick();"),
            "the hand-written adapters' symbols stay declared: {standalone}"
        );
        assert!(
            !standalone.contains("pub struct Clock")
                && !standalone.contains("impl Default for Clock")
                && !standalone.contains("PhantomData"),
            "…but no handle that can do nothing, and no import for one: {standalone}"
        );

        let one = parse_one(
            "#[attributes(service)] api Clock { [manual] now() -> u64 tick() }",
            "clock.def",
        );
        for raw in [None, Some("crate::generated")] {
            let out = RustGen::build_service_wrapper(
                &one,
                &crate::naming::FL,
                raw,
                None,
                "scripts/gen.sh",
            )
            .unwrap()
            .expect("a generated slot earns a module");
            assert!(out.contains("pub struct Clock {"), "{out}");
        }

        if let Some(rustc) = find_rustc() {
            assert!(
                rustc_compiles(
                    rustc,
                    "all_manual_declarations",
                    &format!("#![allow(dead_code)]\n{}", strip_file_header(&standalone))
                ),
                "{standalone}"
            );
        }
    }

    /// The emitted prose is host-agnostic: this backend serves any project whose defs
    /// describe exported symbols, so naming the exporting library - or a flowi-specific
    /// startup call, or a flowi ADR - would be wrong for every project but one.
    #[test]
    fn generated_prose_names_no_particular_host() {
        let def = parse_one(
            "#[attributes(service)] api Clock { now() -> u64 }",
            "clock.def",
        );
        for raw in [None, Some("crate::generated")] {
            let out = RustGen::build_service_wrapper(
                &def,
                &crate::naming::FL,
                raw,
                None,
                "scripts/gen.sh",
            )
            .unwrap()
            .unwrap();
            // The shared SAFETY header says "the linked library", which is the point.
            let prose: String = out
                .lines()
                .filter(|l| {
                    let t = l.trim_start();
                    t.starts_with("//") || t.starts_with("///")
                })
                .collect::<Vec<_>>()
                .join("\n");
            for banned in ["exported by flowi", "base_init", "ADR-", "flowi crate"] {
                assert!(
                    !prose.contains(banned),
                    "generated prose must not name a particular host (`{banned}`): {prose}"
                );
            }
        }
    }

    /// A `*const <primitive>` parameter is a counted buffer with its length outside the
    /// type. Lowering it to &u8 would hand the callee a pointer good for one element
    /// while its contract reads sixteen - an out-of-bounds read driven from safe caller
    /// code - so it is refused on both surfaces.
    #[test]
    fn counted_buffer_param_is_refused_rather_than_lowered_to_one_element() {
        let def = parse_one(
            "#[attributes(service)]\n\
             api Hash { lookup(md5: *const u8) -> bool }",
            "hash.def",
        );
        let err =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap_err();
        assert!(
            err.contains("counted buffer") && err.contains("[slice(u8)]"),
            "the diagnostic names both ways out: {err}"
        );

        let sliced = parse_one(
            "#[attributes(service)]\n\
             api Hash { submit([slice(f32)] samples: *const f32, count: u32) -> u32 }",
            "hash.def",
        );
        let out = RustGen::build_service_wrapper(
            &sliced,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(
            out.contains("pub fn submit(&self, samples: &[f32]) -> u32 {")
                && out.contains("submit(samples.as_ptr(), samples.len() as u32)"),
            "a counted buffer with a `[slice]` marker crosses as a slice, with no \
             no-op cast when the element type already matches the ABI's: {out}"
        );

        // The mutable form collapses the same way, so the pointer and the count cannot
        // disagree.
        let table = parse_one(
            "struct Entry {}\n\
             #[attributes(service)]\n\
             api Reg { publish([slice_mut(Entry)] values: *Entry, count: i32) -> u32 }",
            "reg.def",
        );
        let table_out = RustGen::build_service_wrapper(
            &table,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(
            table_out.contains("pub fn publish(&self, values: &mut [crate::Entry]) -> u32 {")
                && table_out.contains("publish(values.as_mut_ptr(), values.len() as i32)"),
            "{table_out}"
        );

        // The cast is still there when it converts something: the ABI declares `*void`
        // and the marker names what the elements really are.
        let opaque = parse_one(
            "#[attributes(service)]\n\
             api Hash { select([slice(u64)] ids: *const void, count: u64) }",
            "hash.def",
        );
        let opaque_out = RustGen::build_service_wrapper(
            &opaque,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(
            opaque_out.contains("ids.as_ptr() as *const core::ffi::c_void"),
            "{opaque_out}"
        );
    }

    /// A slot handed an arena and answering an optional `#[read]` record forwards
    /// through the generated reader, borrowing the answer from the arena it was
    /// handed. Without the `#[view(...)]` naming the arena's safe reference, the same
    /// slot has no sound spelling and is refused back to `[manual]`.
    #[test]
    fn an_arena_slot_answering_a_read_record_delegates_to_its_reader() {
        const SRC: &str = "#[module(demozoo)]\n\
             #[views(crate::demoscene::data)]\n\
             #[reads(crate::services::demozoo)]\n\
             VIEW\
             extern opaque FlArena\n\
             #[read]\n\
             struct DemozooParty { name: String, found: bool }\n\
             #[attributes(service)]\n\
             api Demozoo {\n\
                 rp_demozoo_get_party(party_id: u32, arena: *FlArena) -> DemozooParty\n\
             }";

        let naming = crate::naming::Naming::new("Rp", "rp");
        let def = parse_one(
            &SRC.replace("VIEW", "#[view(flowi::Arena)]\n"),
            "demozoo.def",
        );
        let defs = [def];
        let model = crate::pairing::resolve(&defs).expect("pairs");
        let out = RustGen::build_service_wrapper(
            &defs[0],
            &naming,
            Some("crate::generated"),
            Some(&ServiceReads {
                model: &model,
                path: "crate::generated",
            }),
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();

        assert!(
            out.contains(
                "pub fn get_party<'a>(&self, party_id: u32, arena: &'a flowi::Arena) \
                 -> Option<crate::services::demozoo::Party<'a>> {"
            ),
            "{out}"
        );
        assert!(
            out.contains(
                "let raw = crate::generated::demozoo::rp_demozoo_get_party(party_id, \
                 arena.as_raw().cast());\n            \
                 crate::generated::demozoo_read::read_demozoo_party(&raw)"
            ),
            "{out}"
        );

        // An arena slot answering something not borrowed from it: the reference anchors
        // no lifetime, so it goes back to `[manual]` rather than emitting an
        // undeclared 'a.
        let unanchored = parse_one(
            &SRC.replace("VIEW", "#[view(flowi::Arena)]\n")
                .replace("-> DemozooParty\n", "-> u32\n"),
            "demozoo.def",
        );
        let unanchored_defs = [unanchored];
        let unanchored_model = crate::pairing::resolve(&unanchored_defs).expect("pairs");
        let err = RustGen::build_service_wrapper(
            &unanchored_defs[0],
            &naming,
            Some("crate::generated"),
            Some(&ServiceReads {
                model: &unanchored_model,
                path: "crate::generated",
            }),
            "scripts/gen.sh",
        )
        .unwrap_err();
        assert!(err.contains("anchors no lifetime"), "{err}");

        let bare = parse_one(&SRC.replace("VIEW", ""), "demozoo.def");
        let bare_defs = [bare];
        let bare_model = crate::pairing::resolve(&bare_defs).expect("pairs");
        let err = RustGen::build_service_wrapper(
            &bare_defs[0],
            &naming,
            Some("crate::generated"),
            Some(&ServiceReads {
                model: &bare_model,
                path: "crate::generated",
            }),
            "scripts/gen.sh",
        )
        .unwrap_err();
        assert!(err.contains("mark the slot `[manual]`"), "{err}");
    }

    /// A record with no found reads back as itself rather than as an Option, so the
    /// slot answering it answers the owned type directly.
    #[test]
    fn an_arena_slot_answering_a_record_without_found_answers_it_directly() {
        let def = parse_one(
            "#[module(demozoo)]\n\
             #[views(crate::demoscene::data)]\n\
             #[reads(crate::services::demozoo)]\n\
             #[view(flowi::Arena)]\n\
             extern opaque FlArena\n\
             struct DemozooTerm { id: u32, name: String }\n\
             #[read]\n\
             struct DemozooTerms { terms: *const DemozooTerm, count: u32 }\n\
             #[attributes(service)]\n\
             api Demozoo {\n\
                 rp_demozoo_get_terms(kind: u32, arena: *FlArena) -> DemozooTerms\n\
             }",
            "demozoo.def",
        );
        let defs = [def];
        let model = crate::pairing::resolve(&defs).expect("pairs");
        let out = RustGen::build_service_wrapper(
            &defs[0],
            &crate::naming::Naming::new("Rp", "rp"),
            Some("crate::generated"),
            Some(&ServiceReads {
                model: &model,
                path: "crate::generated",
            }),
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();

        assert!(
            out.contains(
                "pub fn get_terms<'a>(&self, kind: u32, arena: &'a flowi::Arena) \
                 -> crate::services::demozoo::Terms<'a> {"
            ),
            "{out}"
        );
    }

    /// `[array(T, N)]`: the arg crosses the safe surface as `&[T; N]` and the call
    /// as as_ptr(); the extern declaration keeps the def's raw `*const T`.
    #[test]
    fn array_param_lowers_to_sized_array_reference() {
        let def = parse_one(
            "#[attributes(service)]\n\
             api Hash { hash_lookup([array(u8, 16)] md5: *const u8, subsong: u16) -> u32 }",
            "hash.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            out.contains("pub fn lookup(&self, md5: &[u8; 16], subsong: u16) -> u32 {"),
            "array param is a sized-array reference: {out}"
        );
        assert!(
            out.contains("hash_lookup(md5.as_ptr(), subsong)"),
            "array param crosses as as_ptr(), no count arg: {out}"
        );
        assert!(
            out.contains("md5: *const u8"),
            "extern declaration keeps the raw pointer: {out}"
        );
    }

    /// `[thread_safe]` on every generated slot (rather than the whole block) also earns
    /// the Send + Sync impl; one unmarked slot withholds it.
    #[test]
    fn service_wrapper_thread_safe_per_slot() {
        let all = parse_one(
            "#[attributes(service)]\n\
             api Clock { [thread_safe] now() -> u64 [thread_safe] tick() }",
            "clock.def",
        );
        let all_out =
            RustGen::build_service_wrapper(&all, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            all_out.contains("unsafe impl Send for Clock {}"),
            "all slots thread_safe: {all_out}"
        );

        let mixed = parse_one(
            "#[attributes(service)]\n\
             api Clock { [thread_safe] now() -> u64 tick() }",
            "clock.def",
        );
        let mixed_out = RustGen::build_service_wrapper(
            &mixed,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        assert!(
            !mixed_out.contains("unsafe impl Send"),
            "one unmarked slot withholds Send: {mixed_out}"
        );
    }

    /// The generator hard-fails with a clear diagnostic on any slot it cannot classify -
    /// never a silent guess.
    #[test]
    fn service_wrapper_hard_fails_on_unclassifiable() {
        let cases: &[(&str, &str)] = &[
            (
                "struct Widget {}\n#[attributes(service)] api Bad { get() -> *Widget }",
                "unclassifiable raw-pointer return",
            ),
            (
                "struct Widget {}\n#[attributes(service)] api Bad { [transfer] make() -> *Widget }",
                "must name its destroy slot",
            ),
            (
                "#[attributes(service)] api Bad { poke(p: *void) }",
                "unclassifiable `void` pointer parameter",
            ),
            (
                "struct Widget {}\n#[attributes(service)] api Bad { [transfer(free = nope)] make() -> *Widget }",
                "names no slot in this service",
            ),
            (
                "#[attributes(service)] api Bad { [status] go() }",
                "requires an integer / enum / bool status return",
            ),
            (
                "#[attributes(service)] api Bad { [transfer] make() }",
                "requires a pointer return",
            ),
            (
                "#[attributes(service)] api Bad { [transfer] make() -> u32 }",
                "must be a pointer to a named type",
            ),
            // A `[transfer]` param that is not a pointer (its pointee has a constructor).
            (
                "struct Widget {}\n#[attributes(service)] api Bad {\n\
                 [transfer(free = wf)] make() -> *Widget\n\
                 wf([transfer] w: *Widget)\n\
                 byval([transfer] w: Widget)\n\
                 }",
                "must be a pointer to a named type",
            ),
            // A `[transfer]` param whose pointee has no owning newtype (no constructor).
            (
                "struct Widget {}\n#[attributes(service)] api Bad { use([transfer] w: *Widget) }",
                "has no owning newtype",
            ),
            // A destroy slot with the wrong arity to pair with the transfer return.
            (
                "struct Widget {}\n#[attributes(service)] api Bad {\n\
                 [transfer(free = wf)] make() -> *Widget\n\
                 wf(w: *Widget, mode: u32)\n\
                 }",
                "must take exactly one",
            ),
            // A raw extern opaque pointer parameter cannot be made safe.
            (
                "extern opaque Ctx\n#[attributes(service)] api Bad { poke(c: *const Ctx) }",
                "extern opaque",
            ),
        ];
        for (def_src, needle) in cases {
            let def = parse_one(def_src, "bad.def");
            let err = RustGen::build_service_wrapper(
                &def,
                &crate::naming::FL,
                None,
                None,
                "scripts/gen.sh",
            )
            .expect_err(&format!("expected a hard-fail for: {def_src}"));
            assert!(
                err.contains(needle),
                "diagnostic for `{def_src}` should mention `{needle}`, got: {err}"
            );
        }
    }

    /// A non-service def emits no wrapper module (Ok(None)).
    #[test]
    fn non_service_def_emits_no_wrapper() {
        let def = parse_one("api Cursor { set_visible(visible: bool) }", "cursor.def");
        assert!(RustGen::build_service_wrapper(
            &def,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh"
        )
        .unwrap()
        .is_none());
    }

    /// The unannotated String borrow-for-call default: a String param lowers to
    /// `impl AsRef<str>`, a String return is copied out into an owned String, and
    /// the ABI field crosses the RawStr mirror by value.
    #[test]
    fn service_wrapper_string_lowering() {
        let def = parse_one(
            "#[attributes(service)]\n\
             api Text { greet(name: String) -> String shout(name: String) }",
            "text.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            out.contains("pub fn greet(&self, name: impl AsRef<str>) -> String {")
                && out.contains("crate::RawStr::borrow(name.as_ref())")
                && out.contains("ret.into_string()"),
            "String arg -> &str view, String return -> owned copy: {out}"
        );
        assert!(
            out.contains("pub fn shout(&self, name: impl AsRef<str>) {"),
            "{out}"
        );
        assert!(
            out.contains("pub fn greet(name: crate::RawStr) -> crate::RawStr;"),
            "the exported symbol crosses RawStr by value: {out}"
        );

        if let Some(rustc) = find_rustc() {
            let body = strip_file_header(&out);
            let src = format!(
                "#![allow(dead_code)]\n\
                 #[derive(Clone, Copy)] #[repr(C)] pub struct RawStr {{ pub ptr: *const u8, pub len: usize }}\n\
                 impl RawStr {{\n\
                     fn borrow(s: &str) -> RawStr {{ RawStr {{ ptr: s.as_ptr(), len: s.len() }} }}\n\
                     fn into_string(self) -> String {{ String::new() }}\n\
                 }}\n\
                 {body}"
            );
            assert!(
                rustc_compiles(rustc, "service_wrapper_string", &src),
                "generated String wrapper must compile:\n{src}"
            );
        }
    }

    /// A `[borrowed]` String return keeps the host's view: the wrapper method returns
    /// &str anchored to &self instead of copying into an owned String, and the
    /// site documents the unsafe block's extra invariant.
    #[test]
    fn service_wrapper_borrowed_string_return() {
        let def = parse_one(
            "#[attributes(service)]\n\
             api Focus { [borrowed] focused_id() -> String }",
            "focus.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            out.contains("pub fn focused_id(&self) -> &str {") && out.contains("ret.as_str()"),
            "borrowed String return stays a view: {out}"
        );
        assert!(
            out.contains("// SAFETY: a `[borrowed]` return points at host-owned bytes"),
            "the site documents the borrow's invariant: {out}"
        );

        // The returned lifetime must bind to &self.
        if let Some(rustc) = find_rustc() {
            let body = strip_file_header(&out);
            let src = format!(
                "#![allow(dead_code)]\n\
                 #[derive(Clone, Copy)] #[repr(C)] pub struct RawStr {{ pub ptr: *const u8, pub len: usize }}\n\
                 impl RawStr {{\n\
                     unsafe fn as_str<'a>(&self) -> &'a str {{ \"\" }}\n\
                 }}\n\
                 {body}"
            );
            assert!(
                rustc_compiles(rustc, "service_wrapper_borrowed_string", &src),
                "generated borrowed-String wrapper must compile:\n{src}"
            );
        }
    }

    /// A `[c_only]` slot emits no Rust at all - not an extern declaration, not a
    /// wrapper method - while its unmarked sibling keeps both. The C prototype and
    /// export entry are untouched.
    #[test]
    fn c_only_slot_emits_no_rust_binding_or_wrapper() {
        let def = parse_one(
            "#[attributes(service)]\n\
             api Cat { grab() -> u64 [c_only] grab_named(name: String) -> u64 }",
            "cat.def",
        );
        let mut buf = Vec::new();
        RustGen::generate_api_externs(&mut buf, &def.apis[0]).unwrap();
        let externs = String::from_utf8(buf).unwrap();
        assert!(
            externs.contains("pub fn grab(") && !externs.contains("grab_named"),
            "raw extern block skips the c_only slot: {externs}"
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            out.contains("pub fn grab(&self)") && !out.contains("grab_named"),
            "wrapper skips the c_only slot: {out}"
        );
    }

    /// A `[transfer]` return of a `*const T` produces a `*const`-holding owning newtype.
    #[test]
    fn service_wrapper_const_transfer_return() {
        let def = parse_one(
            "struct Widget {}\n\
             #[attributes(service)]\n\
             api Reg {\n\
                 [transfer(free = release)] acquire() -> *const Widget\n\
                 release([transfer] w: *const Widget)\n\
             }",
            "reg.def",
        );
        let out =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        assert!(
            out.contains("ptr: *const crate::Widget,"),
            "a *const transfer return owns a *const pointer: {out}"
        );
        assert!(
            out.contains("pub fn acquire(&self) -> OwnedWidget {"),
            "{out}"
        );
    }

    /// The vacuous-truth guard on the per-slot thread_safe rule: a block with zero
    /// generated slots must NOT get Send + Sync - an empty "every slot is
    /// thread-safe" is not an audit.
    ///
    /// Driven through write_service_api rather than the module entry point, because
    /// that entry point now drops such a block before it gets here. The guard stays
    /// anyway: it decides whether to emit an unsafe impl, and a decision of that
    /// kind should hold on its own rather than on a filter one call up.
    #[test]
    fn service_wrapper_no_send_without_generated_slots() {
        let def = parse_one(
            "#[attributes(service)] api Empty { [manual] a() [manual] b() }",
            "empty.def",
        );
        let mut out = String::new();
        RustGen::write_service_api(&mut out, &crate::naming::FL, None, &def.apis[0], None).unwrap();
        assert!(
            !out.contains("unsafe impl Send"),
            "no generated slots -> not Send: {out}"
        );
    }

    /// The file-writing entry point fails loud: an unclassifiable slot panics with the
    /// classifier's diagnostic.
    #[test]
    #[should_panic(expected = "unclassifiable raw-pointer return")]
    fn service_wrapper_generate_panics_on_bad_slot() {
        let dir = std::env::temp_dir().join(format!("api_gen_panic_{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let def = parse_one(
            "struct Widget {}\n#[attributes(service)] api Bad { get() -> *Widget }",
            "bad.def",
        );
        let _ = RustGen::generate_service_wrapper(
            dir.to_str().unwrap(),
            &def,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh",
        );
    }

    /// The generated wrapper compiles against a minimal crate-root / FlError
    /// stand-in. The stand-ins sit at the crate root because that is where the consume
    /// surface spells everything it reaches for.
    #[test]
    fn service_wrapper_compiles() {
        let Some(rustc) = find_rustc() else {
            eprintln!("rustc not found; skipping service_wrapper_compiles");
            return;
        };
        let def = parse_one(GADGET_DEF, "gadget.def");
        let module =
            RustGen::build_service_wrapper(&def, &crate::naming::FL, None, None, "scripts/gen.sh")
                .unwrap()
                .unwrap();
        let body = strip_file_header(&module);
        let src = format!(
            "#![allow(dead_code)]\n\
             pub enum Widget {{}}\n\
             pub enum FlError {{ Other(i32) }}\n\
             impl FlError {{\n\
             \x20   pub fn from_status(c: i32) -> Result<(), FlError> {{\n\
             \x20       if c == 0 {{ Ok(()) }} else {{ Err(FlError::Other(c)) }}\n\
             \x20   }}\n\
             }}\n\
             {body}"
        );
        assert!(
            rustc_compiles(rustc, "service_wrapper", &src),
            "generated service wrapper must compile:\n{src}"
        );

        // The shape a project generating both trees gets: no extern "C" block of its
        // own, every call qualified through the raw bindings module. Compiled here
        // because a generator edit that breaks it would otherwise land green in this
        // repo and only fail in the consumer's.
        let forwarding = RustGen::build_service_wrapper(
            &def,
            &crate::naming::FL,
            Some("crate::generated"),
            None,
            "scripts/gen.sh",
        )
        .unwrap()
        .unwrap();
        let body = strip_file_header(&forwarding);
        // The same declarations the --rust-dir backend would have emitted for this
        // def, under the module path the wrapper forwards to.
        let raw_decls: String = def.apis[0]
            .functions
            .iter()
            .filter(|f| !f.has_varargs)
            .map(|f| {
                let (p, r) = RustGen::loose_symbol_sig_parts(
                    LooseSymbolSurface::ExternalConsumer,
                    &f.function_args,
                    f.return_val.as_ref(),
                );
                format!(
                    "    pub fn {}({}){};\n",
                    RustGen::rust_ident(&f.c_name),
                    p,
                    r
                )
            })
            .collect();
        let src = format!(
            "#![allow(dead_code)]\n\
             pub enum Widget {{}}\n\
             pub enum FlError {{ Other(i32) }}\n\
             impl FlError {{\n\
             \x20   pub fn from_status(c: i32) -> Result<(), FlError> {{\n\
             \x20       if c == 0 {{ Ok(()) }} else {{ Err(FlError::Other(c)) }}\n\
             \x20   }}\n\
             }}\n\
             pub mod generated {{ pub mod gadget {{ extern \"C\" {{\n{raw_decls}}} }} }}\n\
             {body}"
        );
        assert!(
            rustc_compiles(rustc, "service_wrapper_forwarding", &src),
            "the forwarding wrapper must compile against the raw tree:\n{src}"
        );
    }

    /// The wired path writes one `<def>.rs` module per service plus the mod.rs index,
    /// and a non-service def contributes nothing.
    #[test]
    fn service_wrapper_wiring_writes_files() {
        let dir = std::env::temp_dir().join(format!("api_gen_wrapper_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let dir_s = dir.to_str().unwrap();

        let svc = parse_one(GADGET_DEF, "gadget.def");
        assert!(RustGen::generate_service_wrapper(
            dir_s,
            &svc,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh"
        )
        .expect("gen svc"));
        assert!(
            dir.join("gadget.rs").exists(),
            "the service module is written"
        );

        let plain = parse_one("api Cursor { set_visible(visible: bool) }", "cursor.def");
        assert!(!RustGen::generate_service_wrapper(
            dir_s,
            &plain,
            &crate::naming::FL,
            None,
            None,
            "scripts/gen.sh"
        )
        .expect("gen plain"));

        RustGen::generate_service_wrapper_mod_file(
            dir_s,
            &["gadget".to_owned()],
            false,
            "scripts/gen.sh",
        )
        .expect("mod file");
        let modrs = std::fs::read_to_string(dir.join("mod.rs")).expect("read mod.rs");
        assert!(
            modrs.contains("pub mod gadget;"),
            "mod.rs indexes the service module: {modrs}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A `#[attributes(Mirror)]` config emits a safe twin - &str for its string
    /// field, `Option<&T>` for its optional pointer, a Default that is the C zero
    /// value, and a to_sys that arena-copies the strings - and every façade slot
    /// taking that config takes the twin instead of the raw ABI struct, so a caller
    /// can build a non-default config without touching flowi_sys.
    #[test]
    fn mirror_config_emits_safe_twin_and_facade_takes_it() {
        let def = parse_one(
            "enum WidgetVariant { Solid = 0, Outline = 1, }\n\
             #[attributes(Mirror)]\n\
             struct WidgetConfig {\n\
                 id_override: String,\n\
                 color: Color,\n\
                 variant: WidgetVariant,\n\
                 focusable: bool,\n\
                 theme_override: *const ThemeOverride,\n\
             }\n\
             api Button {\n\
                 new_impl(label: String, config: WidgetConfig) -> bool\n\
             }",
            "widget_config.def",
        );

        let mut mirror_buf = Vec::new();
        let sdef = def
            .structs
            .iter()
            .find(|s| s.is_mirror())
            .expect("the Mirror struct parses");
        RustGen::generate_mirror_struct(&mut mirror_buf, sdef).expect("mirror");
        let mirror = String::from_utf8(mirror_buf).unwrap();

        assert!(
            mirror.contains("pub struct WidgetConfig<'a> {"),
            "twin carries the borrow: {mirror}"
        );
        assert!(
            mirror.contains("pub id_override: &'a str,"),
            "string field is a &str: {mirror}"
        );
        assert!(
            mirror.contains("pub theme_override: Option<&'a flowi_sys::ThemeOverride>,"),
            "optional pointer is an Option<&T>: {mirror}"
        );
        assert!(
            mirror.contains("pub variant: flowi_sys::WidgetVariant,")
                && mirror.contains("pub focusable: bool,"),
            "by-value fields pass through: {mirror}"
        );
        assert!(
            mirror.contains("id_override: \"\",") && mirror.contains("theme_override: None,"),
            "Default is the C zero default: {mirror}"
        );
        assert!(
            mirror.contains("variant: zero.variant,"),
            "scalar defaults come from the zeroed ABI struct: {mirror}"
        );
        assert!(
            mirror.contains("id_override: { let s = self.id_override; flowi_sys::fl_frame_str(s.as_ptr() as *const core::ffi::c_char, s.len()) },"),
            "to_sys arena-copies the string: {mirror}"
        );
        assert!(
            mirror.contains(
                "theme_override: self.theme_override.map_or(core::ptr::null(), |v| v as *const flowi_sys::ThemeOverride),"
            ),
            "to_sys lowers the reference to a pointer: {mirror}"
        );

        let mut buf = Vec::new();
        let func = &def.apis[0].functions[0];
        RustGen::generate_facade_fn(&mut buf, func).expect("facade");
        let facade = String::from_utf8(buf).unwrap();

        assert!(
            facade.contains(
                "pub fn new(label: impl AsRef<str>, config: crate::generated::widget_config::WidgetConfig<'_>)"
            ),
            "the slot takes the twin, not the ABI struct: {facade}"
        );
        assert!(
            !facade.contains("flowi_sys::WidgetConfig"),
            "the ABI struct must not appear in the signature: {facade}"
        );
        assert!(
            facade.contains("config.to_sys()"),
            "the twin is lowered at the call: {facade}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("mirror facade compile test skipped: no rustc on PATH");
            return;
        };
        // The twin goes where the façade's path expects it, and the config is built
        // from safe code only.
        let src = format!(
            "pub mod flowi_sys {{\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct Color {{ pub r: u8 }}\n\
                #[repr(C)] #[derive(Copy, Clone)] pub enum WidgetVariant {{ Solid = 0, Outline = 1 }}\n\
                #[repr(C)] pub struct ThemeOverride {{ pub slots: u32 }}\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct RawStr {{ pub data: *const core::ffi::c_char, pub packed: u64 }}\n\
                #[repr(C)] pub struct WidgetConfig {{ pub id_override: RawStr, pub color: Color, pub variant: WidgetVariant, pub focusable: bool, pub theme_override: *const ThemeOverride }}\n\
                extern \"C\" {{\n\
                    pub fn fl_frame_str(ptr: *const core::ffi::c_char, len: usize) -> RawStr;\n\
                    pub fn fl_button_impl(label: RawStr, config: WidgetConfig) -> bool;\n\
                }}\n\
             }}\n\
             pub mod generated {{ pub mod widget_config {{ use crate::flowi_sys;\n{mirror}\n }} }}\n\
             pub struct Button;\n\
             impl Button {{\n{facade}}}\n\
             // A caller builds a non-default config naming nothing from flowi_sys.\n\
             pub fn _use() -> bool {{\n\
                 Button::new(\"Save\", crate::generated::widget_config::WidgetConfig {{ id_override: \"save\", ..Default::default() }})\n\
             }}\n",
            mirror = mirror,
            facade = facade,
        );
        assert!(
            rustc_compiles(rustc, "mirror_facade", &src),
            "the generated mirror + façade must compile and be callable from safe code"
        );
    }

    /// A mirrored config that embeds another one spells the field with the nested twin,
    /// defaults it through that twin's own Default, and lowers it by calling its
    /// to_sys - so the whole tree is reachable from safe code and the raw ABI struct
    /// appears nowhere.
    #[test]
    fn nested_mirror_config_lowers_through_the_inner_twin() {
        let def = parse_one(
            "#[attributes(Mirror)]\n\
             struct WidgetConfig { id_override: String, }\n\
             #[attributes(Mirror)]\n\
             struct DropdownConfig {\n\
                 cancel_label: String,\n\
                 min_width: f32,\n\
                 widget: WidgetConfig,\n\
             }\n\
             api Dropdown {\n\
                 new_impl(label: String, config: DropdownConfig)\n\
             }",
            "widget_config.def",
        );

        let mut buf = Vec::new();
        for sdef in def.structs.iter().filter(|s| s.is_mirror()) {
            RustGen::generate_mirror_struct(&mut buf, sdef).expect("mirror");
        }
        let mirror = String::from_utf8(buf).unwrap();

        assert!(
            mirror.contains("pub widget: crate::generated::widget_config::WidgetConfig<'a>,"),
            "the nested field is the inner twin, borrowing the outer parameter: {mirror}"
        );
        assert!(
            mirror.contains("widget: Default::default(),"),
            "the nested default is the inner twin's own: {mirror}"
        );
        assert!(
            mirror.contains("widget: self.widget.to_sys(),"),
            "the nested field lowers through the inner to_sys: {mirror}"
        );
        assert!(
            !mirror.contains("zero.widget"),
            "a nested twin is never read out of the zeroed ABI struct: {mirror}"
        );

        let mut buf = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &def.apis[0].functions[0]).expect("facade");
        let facade = String::from_utf8(buf).unwrap();
        assert!(
            !facade.contains("flowi_sys::DropdownConfig")
                && !facade.contains("flowi_sys::WidgetConfig"),
            "no ABI config reaches the signature: {facade}"
        );

        let Some(rustc) = find_rustc() else {
            eprintln!("nested mirror compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "pub mod flowi_sys {{\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct RawStr {{ pub data: *const core::ffi::c_char, pub packed: u64 }}\n\
                #[repr(C)] pub struct WidgetConfig {{ pub id_override: RawStr }}\n\
                #[repr(C)] pub struct DropdownConfig {{ pub cancel_label: RawStr, pub min_width: f32, pub widget: WidgetConfig }}\n\
                extern \"C\" {{\n\
                    pub fn fl_frame_str(ptr: *const core::ffi::c_char, len: usize) -> RawStr;\n\
                    pub fn fl_dropdown_impl(label: RawStr, config: DropdownConfig);\n\
                }}\n\
             }}\n\
             pub mod generated {{ pub mod widget_config {{ use crate::flowi_sys;\n{mirror}\n }} }}\n\
             pub struct Dropdown;\n\
             impl Dropdown {{\n{facade}}}\n\
             // A caller reaches the nested id override with nothing from flowi_sys.\n\
             pub fn _use() {{\n\
                 use crate::generated::widget_config::{{DropdownConfig, WidgetConfig}};\n\
                 Dropdown::new(\"Preset\", DropdownConfig {{\n\
                     cancel_label: \"Dismiss\",\n\
                     widget: WidgetConfig {{ id_override: \"track-preset\", ..Default::default() }},\n\
                     ..Default::default()\n\
                 }})\n\
             }}\n",
            mirror = mirror,
            facade = facade,
        );
        assert!(
            rustc_compiles(rustc, "nested_mirror", &src),
            "the nested mirror tree must compile and be constructible from safe code"
        );
    }

    /// The unsafe wrapper around a twin's to_sys body tracks direct string fields
    /// only. A field that is itself a twin lowers through its own to_sys, a safe call
    /// carrying its own block, so a config like CheckboxConfig (bool + nested
    /// WidgetConfig) must keep a bare to_sys body. Nothing in the crate denies
    /// warnings, so the compile half's stub crate denies unused_unsafe - a stray
    /// wrapper is then a hard error rather than a warning nobody reads.
    #[test]
    fn mirror_to_sys_wraps_unsafe_only_for_a_direct_string_field() {
        let def = parse_one(
            "#[attributes(Mirror)]\n\
             struct WidgetConfig { id_override: String, }\n\
             #[attributes(Mirror)]\n\
             struct CheckboxConfig {\n\
                 label_on_left: bool,\n\
                 widget: WidgetConfig,\n\
             }\n\
             api Checkbox {\n\
                 new_impl(label: String, config: CheckboxConfig)\n\
             }",
            "widget_config.def",
        );

        // The to_sys body only - a twin's Default has its own, unrelated unsafe
        // (the core::mem::zeroed() the C zero default reads scalars out of).
        let to_sys_body = |name: &str| {
            let sdef = def
                .structs
                .iter()
                .find(|s| s.is_mirror() && s.name == name)
                .expect("mirror");
            let mut buf = Vec::new();
            RustGen::generate_mirror_struct(&mut buf, sdef).expect("mirror");
            let mirror = String::from_utf8(buf).unwrap();
            let (_, body) = mirror.split_once("fn to_sys").expect("to_sys");
            body.to_owned()
        };

        assert!(
            to_sys_body("WidgetConfig").contains("unsafe {"),
            "a direct string field reaches the fl_frame_str extern, so to_sys wraps"
        );
        assert!(
            !to_sys_body("CheckboxConfig").contains("unsafe"),
            "a nested-only twin calls the inner safe to_sys, so its body stays bare"
        );

        let mut buf = Vec::new();
        for sdef in def.structs.iter().filter(|s| s.is_mirror()) {
            RustGen::generate_mirror_struct(&mut buf, sdef).expect("mirror");
        }
        let mirror = String::from_utf8(buf).unwrap();
        let mut buf = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &def.apis[0].functions[0]).expect("facade");
        let facade = String::from_utf8(buf).unwrap();

        let Some(rustc) = find_rustc() else {
            eprintln!("nested-only mirror compile test skipped: no rustc on PATH");
            return;
        };
        let src = format!(
            "#![deny(unused_unsafe)]\n\
             pub mod flowi_sys {{\n\
                #[repr(C)] #[derive(Copy, Clone)] pub struct RawStr {{ pub data: *const core::ffi::c_char, pub packed: u64 }}\n\
                #[repr(C)] pub struct WidgetConfig {{ pub id_override: RawStr }}\n\
                #[repr(C)] pub struct CheckboxConfig {{ pub label_on_left: bool, pub widget: WidgetConfig }}\n\
                extern \"C\" {{\n\
                    pub fn fl_frame_str(ptr: *const core::ffi::c_char, len: usize) -> RawStr;\n\
                    pub fn fl_checkbox_impl(label: RawStr, config: CheckboxConfig);\n\
                }}\n\
             }}\n\
             pub mod generated {{ pub mod widget_config {{ use crate::flowi_sys;\n{mirror}\n }} }}\n\
             pub struct Checkbox;\n\
             impl Checkbox {{\n{facade}}}\n\
             pub fn _use() {{\n\
                 use crate::generated::widget_config::{{CheckboxConfig, WidgetConfig}};\n\
                 Checkbox::new(\"Mute\", CheckboxConfig {{\n\
                     label_on_left: true,\n\
                     widget: WidgetConfig {{ id_override: \"mute\", ..Default::default() }},\n\
                 }})\n\
             }}\n",
            mirror = mirror,
            facade = facade,
        );
        assert!(
            rustc_compiles(rustc, "nested_only_mirror", &src),
            "a nested-only twin must compile with no unused_unsafe (the wrapper stays off)"
        );
    }

    /// A declared `= value` on a bool or numeric field becomes that field's Default;
    /// fields without one keep the C zero default.
    #[test]
    fn mirror_default_uses_declared_field_defaults() {
        let def = parse_one(
            "#[attributes(Mirror)]\n\
             struct TunedConfig { show: bool = true, width: f32 = 200, rows: u32 = 3, gap: f32, }\n\
             api Popup { open(config: TunedConfig) }",
            "tuned_config.def",
        );
        let mut buf = Vec::new();
        let sdef = def.structs.iter().find(|s| s.is_mirror()).expect("mirror");
        RustGen::generate_mirror_struct(&mut buf, sdef).expect("mirror");
        let mirror = String::from_utf8(buf).unwrap();
        assert!(mirror.contains("show: true,"), "bool default: {mirror}");
        assert!(
            mirror.contains("width: 200.0,"),
            "float default gains .0: {mirror}"
        );
        assert!(mirror.contains("rows: 3,"), "integer default: {mirror}");
        assert!(
            mirror.contains("gap: zero.gap,"),
            "undeclared stays zero: {mirror}"
        );
    }

    /// A mirrored config with no borrowed field carries no lifetime - the struct and
    /// both impl blocks are emitted bare, and a referring signature omits `<'_>`.
    #[test]
    fn mirror_without_borrowed_fields_emits_no_lifetime() {
        let def = parse_one(
            "#[attributes(Mirror)]\n\
             struct PlainConfig { z_index: i16, min_width: f32, }\n\
             api Popup { open(config: PlainConfig) }",
            "plain_config.def",
        );

        let mut buf = Vec::new();
        let sdef = def.structs.iter().find(|s| s.is_mirror()).expect("mirror");
        RustGen::generate_mirror_struct(&mut buf, sdef).expect("mirror");
        let mirror = String::from_utf8(buf).unwrap();

        assert!(
            mirror.contains("pub struct PlainConfig {"),
            "no borrow, no lifetime parameter: {mirror}"
        );
        assert!(
            mirror.contains("impl Default for PlainConfig {")
                && mirror.contains("impl PlainConfig {"),
            "the impl blocks name the twin bare: {mirror}"
        );
        assert!(
            !mirror.contains("'a") && !mirror.contains("'_"),
            "no lifetime anywhere in an all-scalar twin: {mirror}"
        );

        let mut buf = Vec::new();
        RustGen::generate_facade_fn(&mut buf, &def.apis[0].functions[0]).expect("facade");
        let facade = String::from_utf8(buf).unwrap();
        assert!(
            facade.contains("pub fn open(config: crate::generated::plain_config::PlainConfig)"),
            "the referring signature omits the borrow too: {facade}"
        );
    }

    fn mod_file(tag: &str, read_modules: &[String], feature: Option<&str>) -> String {
        let dir = std::env::temp_dir().join(format!("api_gen_mod_{}_{}", std::process::id(), tag));
        std::fs::create_dir_all(&dir).expect("create temp dir");

        let mut api_def = ApiDef::default();
        ApiParser::parse_string("#[module(demozoo)]", "demozoo.def", &mut api_def);
        RustGen::generate_mod_file(
            dir.to_str().unwrap(),
            &[&api_def],
            false,
            read_modules,
            feature,
            "scripts/gen.sh",
        )
        .expect("write mod.rs");

        let emitted = std::fs::read_to_string(dir.join("mod.rs")).expect("read mod.rs");
        let _ = std::fs::remove_dir_all(&dir);
        emitted
    }

    /// A reader module is crate-private unless the test feature is on; nothing
    /// else in the tree is conditional.
    #[test]
    fn a_reader_module_is_declared_behind_the_test_feature() {
        let emitted = mod_file("reader", &["demozoo_read".to_owned()], Some("test-readers"));

        assert!(emitted.contains(
            "#[cfg(not(feature = \"test-readers\"))]\n\
             pub(crate) mod demozoo_read;\n\
             #[cfg(feature = \"test-readers\")]\n\
             pub mod demozoo_read;"
        ));
        assert!(emitted.contains("pub mod demozoo;"));
    }

    /// Without the feature name the visibility flip cannot be spelled, so a
    /// reader module without one is refused rather than emitted as public.
    #[test]
    #[should_panic(expected = "reader modules want --read-test-feature")]
    fn a_reader_module_without_a_test_feature_is_refused() {
        mod_file("no_feature", &["demozoo_read".to_owned()], None);
    }

    /// A tree with no readers is unchanged by the feature machinery.
    #[test]
    fn no_reader_modules_needs_no_test_feature() {
        assert!(!mod_file("none", &[], None).contains("cfg(feature"));
    }

    /// `[label(...)]` on every variant emits ALL, name/label and their inverses;
    /// `[reserved]` emits is_reserved; together they compile with the enum.
    #[test]
    fn labelled_and_reserved_enum_emits_lookups_that_compile() {
        let api_def = parse_one(
            "enum Act {\n    [label(\"Shoulder L\")] ShoulderL = 0,\n    \
             [reserved] [label(\"Menu\")] Menu = 1,\n}",
            "act.def",
        );
        let edef = &api_def.enums[0];
        let mut buf = Vec::new();
        RustGen::generate_data_enum(&mut buf, edef).expect("emit enum");
        RustGen::generate_enum_lookups(&mut buf, edef).expect("emit lookups");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(out.contains(
            "pub const ALL: [Act; 2] = [\n        Act::ShoulderL,\n        Act::Menu,\n    ];"
        ));
        assert!(out.contains("            Act::ShoulderL => \"ShoulderL\","));
        assert!(out.contains("            Act::ShoulderL => \"Shoulder L\","));
        assert!(out.contains("pub fn from_label(label: &str) -> Option<Self> {"));
        assert!(out.contains("        matches!(self, Act::Menu)"));

        let Some(rustc) = find_rustc() else {
            eprintln!("labelled enum compile test skipped: no rustc on PATH");
            return;
        };
        assert!(
            rustc_compiles(rustc, "labelled_enum", &out),
            "generated lookups must compile: {out}"
        );
    }

    #[test]
    fn plain_enum_emits_no_lookups() {
        let api_def = parse_one("enum Plain { A = 0, B = 1, }", "plain.def");
        let mut buf = Vec::new();
        RustGen::generate_enum_lookups(&mut buf, &api_def.enums[0]).expect("emit");
        assert!(buf.is_empty());
    }
}
