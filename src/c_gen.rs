// C generation.
//
// api_gen emits a real typedef enum/typedef struct per def into
// `flowi/include/flowi/<module>/<name>.h` (generate_header). An `api <Domain>`
// block additionally emits the direct `fl_*(...)` function prototypes plus the
// designated-initializer / varargs call macros that route to them.
//
// All generated C names flow from the Naming profile (naming.rs). No
// clang-format post-pass - output is hand-canonicalised for no-op regen.

use crate::api_parser::*;
use crate::naming::Naming;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

pub struct Cgen;

impl Cgen {
    fn write_comment<W: Write>(f: &mut W, comments: &[String], indent: usize) -> io::Result<()> {
        for c in comments {
            // A blank line inside a multi-paragraph doc block emits a bare //
            // (no trailing space).
            if c.is_empty() {
                writeln!(f, "{:indent$}//", "", indent = indent)?;
            } else {
                writeln!(f, "{:indent$}// {}", "", c, indent = indent)?;
            }
        }
        Ok(())
    }

    /// Emit the typedef header for a def: a self-contained
    /// `flowi/include/flowi/<module>/<name>.h` defining every real enum then struct
    /// the def authors (enums first - a struct field may reference one). The
    /// per-module subdir (`<root>/<module>/`) is created on demand.
    #[allow(clippy::too_many_arguments)]
    pub fn generate_header(
        c_include_root: &str,
        api_def: &ApiDef,
        type_loc: &BTreeMap<String, (String, String)>,
        naming: &Naming,
        include_prefix: Option<&str>,
        extern_c: bool,
        layout_asserts: Option<&crate::layout::TypeRegistry>,
        script: &str,
    ) -> io::Result<()> {
        let module_dir = format!("{}/{}", c_include_root, api_def.module.as_str());
        std::fs::create_dir_all(&module_dir)?;
        let filename = format!("{}/{}.h", module_dir, api_def.base_filename);
        let mut f = BufWriter::new(File::create(&filename)?);

        let fwd_decl_structs = Self::structs_needing_forward_decl(api_def);

        write!(f, "{}", crate::emit_util::header(script))?;
        writeln!(f)?;
        writeln!(f, "#pragma once")?;
        writeln!(f)?;
        let pinned: Vec<(String, crate::layout::StructLayout)> = match layout_asserts {
            Some(registry) => Self::pinned_layouts(api_def, registry, naming),
            None => Vec::new(),
        };
        let mut includes: Vec<String> = Vec::new();
        // The layout pins spell static_assert (C11 <assert.h>, a keyword in
        // C++11) and offsetof (<stddef.h>).
        if !pinned.is_empty() {
            includes.push("#include <assert.h>".to_owned());
        }
        if Self::header_needs_stdbool(api_def) {
            includes.push("#include <stdbool.h>".to_owned());
        }
        if Self::header_needs_stdint(api_def) {
            includes.push("#include <stdint.h>".to_owned());
        }
        if Self::header_needs_stddef(api_def) || !pinned.is_empty() {
            includes.push("#include <stddef.h>".to_owned());
        }
        if Self::header_needs_string(api_def) {
            includes.push(match naming.string_include.as_deref() {
                Some(path) => format!("#include <{}>", path),
                None => cross_include(include_prefix, "core", "string"),
            });
        }
        includes.extend(Self::header_dep_includes(api_def, type_loc, include_prefix));
        includes.extend(Self::mod_includes(api_def, include_prefix));
        // An api block's prototypes carry the profile's export-annotation macro
        // (FL_API / RP_API), so pull in the header that defines it.
        if api_def.has_apis() {
            let api_header = naming.c_api_header();
            let fl_api_include = match include_prefix {
                Some(prefix) => format!("#include <{}/{}>", prefix, api_header),
                None => format!("#include \"{}\"", api_header),
            };
            includes.insert(0, fl_api_include);
        }
        for inc in &includes {
            writeln!(f, "{}", inc)?;
        }
        if !includes.is_empty() {
            writeln!(f)?;
        }

        for (name, value) in &api_def.consts {
            writeln!(f, "#define {} {}", name, value)?;
        }
        if !api_def.consts.is_empty() {
            writeln!(f)?;
        }

        // C++ consumers need every public declaration to retain C linkage.
        if extern_c {
            writeln!(f, "#ifdef __cplusplus")?;
            writeln!(f, "extern \"C\" {{")?;
            writeln!(f, "#endif")?;
            writeln!(f)?;
        }

        Self::generate_header_types(&mut f, api_def, naming, &fwd_decl_structs)?;

        Self::generate_layout_pins(&mut f, &pinned)?;

        // After the domain's own types, so the signatures can name them.
        for api in &api_def.apis {
            Self::generate_api_decls(&mut f, api, naming)?;
        }

        if extern_c {
            writeln!(f)?;
            writeln!(f, "#ifdef __cplusplus")?;
            writeln!(f, "}}")?;
            writeln!(f, "#endif")?;
        }

        Ok(())
    }

    /// Emit a def's real types into its header, in the one order C accepts: enums,
    /// extern opaque forward-decls, struct forward-decls for recursive clusters,
    /// then the callbacks and the structs (with any struct a callback names by value
    /// hoisted ahead of it).
    fn generate_header_types<W: Write>(
        f: &mut W,
        api_def: &ApiDef,
        naming: &Naming,
        fwd_decl_structs: &BTreeSet<String>,
    ) -> io::Result<()> {
        for enum_def in &api_def.enums {
            if enum_def.is_real_type() {
                Self::generate_enum(f, enum_def, naming)?;
            }
        }
        // Forward-declare each extern opaque dep before the structs that name it by
        // pointer. No `#include`, no body - the header never dereferences these.
        for ext in &api_def.externs {
            Self::generate_extern_opaque_forward_decl(f, ext)?;
        }
        // A struct field naming another generated real struct by pointer must have
        // that struct's typedef name already in scope. When the target is defined at
        // or after the referrer, emit a typedef struct FlX FlX; forward-decl
        // up-front; re-typedefing the same tag in the body is valid C11/C23.
        for sdef in api_def
            .structs
            .iter()
            .filter(|s| fwd_decl_structs.contains(s.name.as_str()))
        {
            Self::generate_struct_forward_decl(f, sdef, naming)?;
        }
        // A `callback <Name>` that takes a generated struct by value needs that
        // struct's full definition before the callback typedef - a function-pointer
        // typedef naming an as-yet-undeclared struct type by value is not valid C.
        let cb_value_structs: BTreeSet<&str> = api_def
            .callbacks
            .iter()
            .flat_map(|cb| cb.function_args.iter().chain(cb.return_val.iter()))
            .filter(|v| !v.pointer && !v.const_pointer)
            .map(|v| v.type_name.as_str())
            .collect();
        for sdef in api_def
            .structs
            .iter()
            .filter(|s| cb_value_structs.contains(s.name.as_str()))
        {
            Self::generate_struct_decl(f, sdef, naming)?;
        }
        // Before the remaining structs, so a struct field may reference a callback
        // typedef.
        for cb in &api_def.callbacks {
            Self::generate_callback_typedef(f, cb, naming)?;
        }
        for sdef in api_def
            .structs
            .iter()
            .filter(|s| !cb_value_structs.contains(s.name.as_str()))
        {
            Self::generate_struct_decl(f, sdef, naming)?;
        }

        Ok(())
    }

    /// Dispatch a struct def to its real-type emitter: a handle typedef, an opaque
    /// forward-decl, or a full struct body.
    fn generate_struct_decl<W: Write>(f: &mut W, sdef: &Struct, naming: &Naming) -> io::Result<()> {
        if sdef.is_handle_type {
            Self::generate_handle_typedef(f, sdef, naming)
        } else if sdef.is_opaque() {
            Self::generate_opaque_forward_decl(f, sdef, naming)
        } else if sdef.is_real_type() {
            Self::generate_struct(f, sdef, naming)
        } else {
            Ok(())
        }
    }

    /// Whether a header needs `<stdint.h>`: a handle typedefs a fixed-width int
    /// (uint32_t), and any value of a fixed-width primitive type names a stdint
    /// type. An enum, another generated struct, an external type or an opaque
    /// forward-decl does not.
    fn header_needs_stdint(api_def: &ApiDef) -> bool {
        let struct_needs = api_def
            .structs
            .iter()
            .filter(|s| s.emits_typedef_header())
            .any(|s| {
                s.is_handle_type
                    || s.variables
                        .iter()
                        .any(|v| v.vtype == VariableType::Primitive)
            });
        let api_needs = api_value_iter(api_def).any(is_fixed_width_primitive);
        let fn_field_needs = struct_fn_field_values(api_def).any(is_fixed_width_primitive);
        let callback_needs = callback_values(api_def).any(is_fixed_width_primitive);
        struct_needs || api_needs || fn_field_needs || callback_needs
    }

    /// Whether a header needs `<stdbool.h>`: bool is a C99 library type, not a
    /// keyword in the C11/C17 dialect flowi compiles, so a header that names it must
    /// pull the include to stay self-contained.
    fn header_needs_stdbool(api_def: &ApiDef) -> bool {
        let struct_needs = api_def
            .structs
            .iter()
            .filter(|s| s.emits_typedef_header())
            .any(|s| s.variables.iter().any(is_bool_value));
        let api_needs = api_value_iter(api_def).any(is_bool_value);
        let fn_field_needs = struct_fn_field_values(api_def).any(is_bool_value);
        let callback_needs = callback_values(api_def).any(is_bool_value);
        struct_needs || api_needs || fn_field_needs || callback_needs
    }

    /// Whether a header names FlString. It is the one base type api_gen does not
    /// author - a hand-written public header defines it - and it crosses by value,
    /// so the definition must be in scope before the slot that names it.
    fn header_needs_string(api_def: &ApiDef) -> bool {
        let struct_needs = api_def
            .structs
            .iter()
            .filter(|s| s.emits_typedef_header())
            .any(|s| s.variables.iter().any(is_string_value));
        let api_needs = api_value_iter(api_def).any(is_string_value);
        let fn_field_needs = struct_fn_field_values(api_def).any(is_string_value);
        let callback_needs = callback_values(api_def).any(is_string_value);
        struct_needs || api_needs || fn_field_needs || callback_needs
    }

    /// Whether a header needs `<stddef.h>`: a usize/isize value
    /// (size_t/ptrdiff_t) names a `<stddef.h>` type.
    fn header_needs_stddef(api_def: &ApiDef) -> bool {
        let struct_needs = api_def
            .structs
            .iter()
            .filter(|s| s.emits_typedef_header())
            .any(|s| s.variables.iter().any(is_stddef_primitive));
        let api_needs = api_value_iter(api_def).any(is_stddef_primitive);
        let fn_field_needs = struct_fn_field_values(api_def).any(is_stddef_primitive);
        let callback_needs = callback_values(api_def).any(is_stddef_primitive);
        struct_needs || api_needs || fn_field_needs || callback_needs
    }

    /// The other generated headers this def's header must include to be
    /// self-contained: one `#include <flowi/<module>/<stem>.h>` per authored type
    /// (struct or enum) named by a struct field (union arms included) or api slot
    /// whose defining def is not this one. Each dependency is spelled by its owner's
    /// public path (its `#[module]` + header stem). Base/external types (FlString,
    /// `Rp*`) are not in type_loc, so they stay includer-provided by convention.
    /// Sorted for deterministic output.
    fn header_dep_includes(
        api_def: &ApiDef,
        type_loc: &BTreeMap<String, (String, String)>,
        include_prefix: Option<&str>,
    ) -> Vec<String> {
        let mut includes: BTreeSet<String> = BTreeSet::new();
        let referenced = api_def
            .structs
            .iter()
            .flat_map(|s| s.variables.iter())
            .flat_map(with_union_arms)
            .chain(api_value_iter(api_def))
            .chain(struct_fn_field_values(api_def))
            .chain(callback_values(api_def));
        for v in referenced {
            if let Some((module, stem)) = type_loc.get(&v.type_name) {
                if stem != &api_def.base_filename {
                    includes.insert(cross_include(include_prefix, module, stem));
                }
            }
        }
        includes.into_iter().collect()
    }

    /// The hand-written public headers this def pulls in via `mod <name>`: one
    /// `#include <flowi/<module>/<name>.h>` per directive, against this def's own
    /// public module root. Unlike header_dep_includes these are not derived from
    /// referenced types - the type they define is authored by hand, so it never
    /// appears in type_loc. Declaration order is preserved.
    fn mod_includes(api_def: &ApiDef, include_prefix: Option<&str>) -> Vec<String> {
        api_def
            .mods
            .iter()
            .map(|m| cross_include(include_prefix, &api_def.module, m))
            .collect()
    }

    /// The structs this header pins, paired with their IDL-computed layout. Only
    /// real (body-emitting) structs qualify - a handle is an integer typedef and
    /// an opaque type has no body here to measure. A struct carrying an anonymous
    /// union is skipped: offsetof cannot name an unnamed member, so pinning it
    /// would need a different shape than the field walk below.
    fn pinned_layouts(
        api_def: &ApiDef,
        registry: &crate::layout::TypeRegistry,
        naming: &Naming,
    ) -> Vec<(String, crate::layout::StructLayout)> {
        api_def
            .structs
            .iter()
            .filter(|s| s.is_real_type() && s.emits_typedef_header())
            .filter(|s| !s.variables.iter().any(|v| v.union_variants.is_some()))
            .map(|s| (naming.c_type(&s.name), registry.layout_for(s)))
            .collect()
    }

    /// Emit the C layout pins: the size and per-field offsets api_gen computed for
    /// each struct above, checked against what this compiler actually lays out. They
    /// guard against api_gen's LP64 layout model disagreeing with the target, which
    /// the generated Rust binding's own assertions rest on.
    fn generate_layout_pins<W: Write>(
        f: &mut W,
        pinned: &[(String, crate::layout::StructLayout)],
    ) -> io::Result<()> {
        if pinned.is_empty() {
            return Ok(());
        }
        writeln!(
            f,
            "// Layout pins - the IDL-computed layout of the types above,"
        )?;
        writeln!(f, "// checked against what this compiler produces.")?;
        for (name, layout) in pinned {
            writeln!(
                f,
                "static_assert(sizeof({}) == {}, \"{} size drift\");",
                name, layout.size, name
            )?;
            for field in &layout.fields {
                writeln!(
                    f,
                    "static_assert(offsetof({}, {}) == {}, \"{}.{} offset drift\");",
                    name, field.name, field.offset, name, field.name
                )?;
            }
        }
        writeln!(f)
    }

    /// Emit a handle's typedef + invalid-sentinel `#define` into the real-type
    /// header (typedef uint32_t FlImageHandle; + `#define FL_IMAGE_HANDLE_INVALID
    /// 0xFFFFFFFF`). The underlying width and sentinel value come from
    /// `#[handle(...)]`; a bare `#[attributes(Handle)]` (no spec) keeps the legacy
    /// uint64_t typedef with no sentinel.
    fn generate_handle_typedef<W: Write>(
        f: &mut W,
        sdef: &Struct,
        naming: &Naming,
    ) -> io::Result<()> {
        Self::write_comment(f, &sdef.doc_comments, 0)?;
        let name = naming.c_type(&sdef.name);
        match &sdef.handle {
            Some(spec) => {
                writeln!(f, "typedef {} {};", c_primitive(&spec.int_type), name)?;
                writeln!(
                    f,
                    "#define {} {}",
                    naming.c_handle_sentinel(&sdef.name),
                    spec.invalid
                )?;
            }
            None => writeln!(f, "typedef uint64_t {};", name)?,
        }
        writeln!(f)
    }

    /// Emit an opaque type's forward-declaration into the real-type header
    /// (typedef struct FlTextInputState FlTextInputState;). The real struct
    /// body lives in a hand-written internal header; api_gen only names the type so
    /// it can cross the API behind a pointer.
    fn generate_opaque_forward_decl<W: Write>(
        f: &mut W,
        sdef: &Struct,
        naming: &Naming,
    ) -> io::Result<()> {
        Self::write_comment(f, &sdef.doc_comments, 0)?;
        let name = naming.c_type(&sdef.name);
        writeln!(f, "typedef struct {} {};", name, name)?;
        writeln!(f)
    }

    /// Emit a real struct's forward-declaration (typedef struct FlJsonValue
    /// FlJsonValue;). The full body still follows below; re-typedefing the same tag
    /// to the same type is valid C11/C23.
    fn generate_struct_forward_decl<W: Write>(
        f: &mut W,
        sdef: &Struct,
        naming: &Naming,
    ) -> io::Result<()> {
        let name = naming.c_type(&sdef.name);
        writeln!(f, "typedef struct {} {};", name, name)?;
        writeln!(f)
    }

    /// Names of the real structs that need an up-front forward-decl: a struct in
    /// this def whose typedef name is referenced by pointer from a field -
    /// union arms included - of a struct defined at or after it (a self-ref or
    /// forward-ref), or from a callback typedef's args/return. Backward-refs
    /// compile without one. A callback names its pointer deps unconditionally: the
    /// callback typedefs are emitted ahead of the structs, so every struct a
    /// callback points at is a forward-ref from where the typedef sits.
    fn structs_needing_forward_decl(api_def: &ApiDef) -> BTreeSet<String> {
        let index: BTreeMap<&str, usize> = api_def
            .structs
            .iter()
            .enumerate()
            .filter(|(_, s)| s.is_real_type())
            .map(|(i, s)| (s.name.as_str(), i))
            .collect();
        let mut needed: BTreeSet<String> = BTreeSet::new();
        for (referrer_idx, sdef) in api_def.structs.iter().enumerate() {
            if !sdef.is_real_type() {
                continue;
            }
            for var in sdef.variables.iter().flat_map(with_union_arms) {
                if !(var.pointer || var.const_pointer) || var.is_extern_opaque || var.is_callback {
                    continue;
                }
                if let Some(&target_idx) = index.get(var.type_name.as_str()) {
                    if target_idx >= referrer_idx {
                        needed.insert(var.type_name.clone());
                    }
                }
            }
        }
        for var in api_def
            .callbacks
            .iter()
            .flat_map(|cb| cb.function_args.iter().chain(cb.return_val.iter()))
        {
            if !(var.pointer || var.const_pointer) || var.is_extern_opaque || var.is_callback {
                continue;
            }
            if index.contains_key(var.type_name.as_str()) {
                needed.insert(var.type_name.clone());
            }
        }
        needed
    }

    /// Emit an extern opaque dep's forward-declaration
    /// (typedef struct UiCtx UiCtx;). The name is the verbatim external C type (no
    /// Fl prefix) and no body / `#include` is emitted.
    fn generate_extern_opaque_forward_decl<W: Write>(
        f: &mut W,
        ext: &ExternType,
    ) -> io::Result<()> {
        Self::write_comment(f, &ext.doc_comments, 0)?;
        writeln!(f, "typedef struct {} {};", ext.name, ext.name)?;
        writeln!(f)
    }

    /// C spelling of a value's base type (no pointer qualifier): the string type
    /// (FlString) and every other named type flow through the naming profile
    /// (Color -> FlColor); primitives map via stdint. The one verbatim path is
    /// an extern opaque dep: it names an external C type that owns its real
    /// spelling, so the profile prefix is not applied (UiCtx stays UiCtx).
    fn c_base_type(var: &Variable, naming: &Naming) -> String {
        if var.is_extern_opaque {
            return var.type_name.clone();
        }
        match var.vtype {
            VariableType::Str => naming.c_string_type(),
            VariableType::Primitive => var.get_c_primitive_type().into_owned(),
            _ => naming.c_type(&var.type_name),
        }
    }

    /// Apply a value's pointer qualifier to its base C type (`const T*` / `T*`).
    fn apply_c_pointer(var: &Variable, base: String) -> String {
        if var.const_pointer {
            format!("const {}*", base)
        } else if var.pointer {
            format!("{}*", base)
        } else {
            base
        }
    }

    /// C spelling of a method arg / return value: route through c_base_type,
    /// then apply any pointer qualifier.
    fn c_value_type(var: &Variable, naming: &Naming) -> String {
        Self::apply_c_pointer(var, Self::c_base_type(var, naming))
    }

    // -------------------------------------------------------------------------
    // Real-type C definitions. Plain structs route here; handles and opaque types
    // have their own emitters.
    // -------------------------------------------------------------------------

    fn c_field_type(var: &Variable, naming: &Naming) -> String {
        Self::apply_c_pointer(var, Self::c_base_type(var, naming))
    }

    fn generate_struct<W: Write>(f: &mut W, sdef: &Struct, naming: &Naming) -> io::Result<()> {
        Self::write_comment(f, &sdef.doc_comments, 0)?;

        let name = naming.c_type(&sdef.name);
        writeln!(f, "typedef struct {} {{", name)?;
        // Value + function fields in authored order: a vtable may carry a value field
        // after its function-pointers, and preserving the order keeps the generated
        // struct byte-identical to the hand-written one.
        for field in sdef.ordered_fields() {
            match field {
                FieldRef::Var(i) => {
                    let var = &sdef.variables[i];
                    Self::write_comment(f, &var.doc_comments, 4)?;
                    if let Some(variants) = &var.union_variants {
                        // A named field (size: union {...}) emits } size;; an
                        // unnamed one emits a C11 anonymous union member (};), whose
                        // arms are reached directly off the struct (event.move.x).
                        writeln!(f, "    union {{")?;
                        for member in variants {
                            Self::write_comment(f, &member.doc_comments, 8)?;
                            writeln!(
                                f,
                                "        {} {};",
                                Self::c_field_type(member, naming),
                                member.name
                            )?;
                        }
                        if var.name.is_empty() {
                            writeln!(f, "    }};")?;
                        } else {
                            writeln!(f, "    }} {};", var.name)?;
                        }
                    } else {
                        // A fixed-size array field spells `type name[N];` - the size
                        // suffix attaches to the declarator, not the type.
                        let array = match &var.array {
                            Some(ArrayType::SizedArray(n)) => format!("[{}]", n),
                            _ => String::new(),
                        };
                        writeln!(
                            f,
                            "    {} {}{};",
                            Self::c_field_type(var, naming),
                            var.name,
                            array
                        )?;
                    }
                }
                FieldRef::Func(i) => {
                    let func = &sdef.functions[i];
                    Self::write_comment(f, &func.doc_comments, 4)?;
                    writeln!(
                        f,
                        "    {} (*{})({});",
                        Self::c_return_type(func, naming),
                        func.name,
                        Self::c_api_params(func, naming)
                    )?;
                }
            }
        }
        writeln!(f, "}} {};\n", name)
    }

    fn generate_enum<W: Write>(f: &mut W, enum_def: &Enum, naming: &Naming) -> io::Result<()> {
        Self::write_comment(f, &enum_def.doc_comments, 0)?;

        let name = naming.c_type(&enum_def.name);
        // A packed IDL enum is byte-sized on the Rust side (`#[repr(u8)]`); the
        // GCC/Clang packed attribute makes the C enum 1 byte too, where a plain
        // int-sized enum would inflate every struct that embeds it.
        let packed = if enum_def.is_packed {
            " __attribute__((__packed__))"
        } else {
            ""
        };
        // Enumerator constants spell `<Prefix><Stem>_<Variant>`, the stem defaulting
        // to the enum's own name (Key -> FlKey_A).
        let stem = enum_def
            .enumerator_override
            .as_deref()
            .unwrap_or(&enum_def.name);
        writeln!(f, "typedef enum{} {} {{", packed, name)?;
        for entry in &enum_def.entries {
            Self::write_comment(f, &entry.doc_comments, 4)?;
            if let Some(value) = enum_def
                .entry_value_literal(entry)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
            {
                writeln!(
                    f,
                    "    {} = {},",
                    naming.c_enumerator(stem, &entry.name),
                    value
                )?;
            }
        }
        writeln!(f, "}} {};\n", name)
    }

    // -------------------------------------------------------------------------
    // API construct. One `api <Domain>` block emits, into the domain's typedef
    // header: the direct `fl_<domain>_<fn>(...)` prototypes (hand-written bodies) and
    // the convenience/varargs call macros routing to them.
    // -------------------------------------------------------------------------

    /// C spelling of an api slot's return type (void when none).
    fn c_return_type(func: &Function, naming: &Naming) -> String {
        Self::c_return_of(func.return_val.as_ref(), naming)
    }

    /// C spelling of a return value (void when none) - the shared core of
    /// [`c_return_type`], reused by callback typedefs.
    fn c_return_of(ret: Option<&Variable>, naming: &Naming) -> String {
        match ret {
            Some(v) => Self::c_value_type(v, naming),
            None => "void".to_owned(),
        }
    }

    /// C parameter list for an api slot / its hand-written body: the explicit args
    /// spelled by their value type, a trailing ... for a varargs slot, and
    /// void for the empty list.
    fn c_api_params(func: &Function, naming: &Naming) -> String {
        Self::c_param_list(&func.function_args, func.has_varargs, naming)
    }

    /// C parameter list from a bare arg list - the shared core of [`c_api_params`],
    /// reused by callback typedefs (which carry no varargs).
    fn c_param_list(args: &[Variable], has_varargs: bool, naming: &Naming) -> String {
        let mut parts: Vec<String> = Vec::new();
        for a in args.iter().filter(|a| a.vtype != VariableType::SelfType) {
            match &a.array {
                // An `[*const T]` / `[*T]` array arg lowers to a pointer plus an auto
                // `<name>_size` length companion. Const-ness follows the IDL
                // qualifier: `[*const T]` is an input, `[*T]` a mutable buffer.
                Some(ArrayType::Unsized) => {
                    let base = Self::c_base_type(a, naming);
                    let ptr = if a.pointer {
                        format!("{}*", base)
                    } else {
                        format!("const {}*", base)
                    };
                    parts.push(format!("{} {}", ptr, a.name));
                    parts.push(format!("uint32_t {}_size", a.name));
                }
                Some(ArrayType::SizedArray(n)) => {
                    parts.push(format!(
                        "{} {}[{}]",
                        Self::c_base_type(a, naming),
                        a.name,
                        n
                    ));
                }
                None => parts.push(format!("{} {}", Self::c_value_type(a, naming), a.name)),
            }
        }
        if has_varargs {
            parts.push("...".to_owned());
        }
        if parts.is_empty() {
            "void".to_owned()
        } else {
            parts.join(", ")
        }
    }

    /// Emit a `callback <Name>` construct as a C function-pointer typedef:
    /// `typedef ret (*Fl<Name>)(args);`.
    fn generate_callback_typedef<W: Write>(
        f: &mut W,
        cb: &Callback,
        naming: &Naming,
    ) -> io::Result<()> {
        Self::write_comment(f, &cb.doc_comments, 0)?;
        writeln!(
            f,
            "typedef {} (*{})({});",
            Self::c_return_of(cb.return_val.as_ref(), naming),
            naming.c_type(&cb.name),
            Self::c_param_list(&cb.function_args, false, naming)
        )?;
        writeln!(f)
    }

    /// Emit an `api <Domain>` block's declarations into the typedef header: the
    /// direct `fl_<domain>_<fn>(...)` function prototypes. _impl config slots also
    /// get their lowercase convenience macro.
    fn generate_api_decls<W: Write>(f: &mut W, api: &Api, naming: &Naming) -> io::Result<()> {
        Self::write_comment(f, &api.doc_comments, 0)?;
        writeln!(f, "// Direct API - hand-written bodies.")?;
        for func in &api.functions {
            Self::write_comment(f, &func.doc_comments, 0)?;
            writeln!(
                f,
                "{} {} {}({});",
                naming.c_api_macro(),
                Self::c_return_type(func, naming),
                func.c_name,
                Self::c_api_params(func, naming)
            )?;
        }
        writeln!(f)?;

        for func in &api.functions {
            // A `#[attributes(service)]` block's by-value struct params are whole
            // values threaded in, not { .field = ... } configs, so a designated-init
            // convenience macro would shadow the real function and rewrite
            // sb_clear(sb) into sb_clear((FlStringBuilder){ sb }), a type error.
            // The same is true of a `[scope_end]` slot on any block.
            if !api.is_service && !func.is_scope_end && convenience_config_arg(func).is_some() {
                if func.c_name.ends_with("_impl") {
                    Self::generate_convenience_macro(f, func, naming)?;
                } else {
                    let typed_name = Self::typed_call_macro_name(func);
                    let direct_callee = format!("({})", func.c_name);
                    Self::generate_named_plain_call_macro(
                        f,
                        func,
                        &typed_name,
                        &direct_callee,
                        false,
                    )?;
                    writeln!(f, "#ifndef FL_API_IMPLEMENTATION")?;
                    Self::generate_convenience_macro(f, func, naming)?;
                    writeln!(f, "#endif")?;
                    writeln!(f)?;
                }
            }
        }

        Ok(())
    }

    /// Emit a slot's designated-initializer convenience macro, routing directly to
    /// its `fl_*` body:
    /// `#define fl_cursor_set(...) fl_cursor_set((FlCursor) { __VA_ARGS__ })`.
    /// The trailing by-value config struct is built from __VA_ARGS__; any leading
    /// args stay explicit.
    ///
    /// An _impl slot's macro is the body name with _impl stripped
    /// (fl_menu_radio) forwarding to the _impl body (fl_menu_radio_impl). A
    /// non-_impl slot keeps its lowercase function spelling; the C preprocessor
    /// suppresses recursive expansion while its replacement is active.
    fn generate_convenience_macro<W: Write>(
        f: &mut W,
        func: &Function,
        naming: &Naming,
    ) -> io::Result<()> {
        Self::generate_convenience_call_macro(f, func, naming, &func.c_name, false, true)
    }

    fn generate_convenience_call_macro<W: Write>(
        f: &mut W,
        func: &Function,
        naming: &Naming,
        callee: &str,
        hygienic: bool,
        emit_comment: bool,
    ) -> io::Result<()> {
        let cfg =
            convenience_config_arg(func).expect("generate_convenience_macro without a config arg");
        // The leading args (everything before the trailing config struct) stay
        // explicit; identity-compare against cfg to drop exactly that one arg.
        let leading: Vec<&Variable> = func
            .function_args
            .iter()
            .filter(|a| a.vtype != VariableType::SelfType)
            .filter(|a| !std::ptr::eq(*a, cfg))
            .collect();

        // A `[*const T]` slice lowers to a pointer plus an auto `<name>_size` length
        // companion (mirrors c_api_params), so the macro must take and forward both.
        let leading_tokens = Self::c_macro_arg_tokens(leading.into_iter(), hygienic);

        let mut macro_params: Vec<String> = leading_tokens.clone();
        macro_params.push("...".to_owned());

        // The compound literal is spelled by the slot's own value type, so it matches
        // the function parameter exactly.
        let mut call_args: Vec<String> = leading_tokens;
        call_args.push(format!(
            "({}) {{ __VA_ARGS__ }}",
            Self::c_value_type(cfg, naming)
        ));

        let macro_name = Self::convenience_call_macro_name(func);

        if emit_comment {
            writeln!(
                f,
                "// Designated-initializer convenience macro - routes directly to the fl_* body."
            )?;
        }
        writeln!(
            f,
            "#define {}({}) {}({})",
            macro_name,
            macro_params.join(", "),
            callee,
            call_args.join(", ")
        )?;
        writeln!(f)?;
        Ok(())
    }

    fn convenience_call_macro_name(func: &Function) -> String {
        match func.c_name.strip_suffix("_impl") {
            Some(call_name) => call_name.to_owned(),
            None => func.c_name.clone(),
        }
    }

    fn typed_call_macro_name(func: &Function) -> String {
        if func.c_name.ends_with("_impl") {
            func.c_name.clone()
        } else {
            format!("{}_impl", func.c_name)
        }
    }

    fn c_macro_arg_name(name: &str, hygienic: bool) -> String {
        if hygienic {
            format!("_fl_{name}")
        } else {
            name.to_owned()
        }
    }

    fn c_macro_arg_tokens<'a>(
        args: impl Iterator<Item = &'a Variable>,
        hygienic: bool,
    ) -> Vec<String> {
        args.flat_map(|arg| match &arg.array {
            Some(ArrayType::Unsized) => vec![
                Self::c_macro_arg_name(&arg.name, hygienic),
                Self::c_macro_arg_name(&format!("{}_size", arg.name), hygienic),
            ],
            _ => vec![Self::c_macro_arg_name(&arg.name, hygienic)],
        })
        .collect()
    }

    fn generate_named_plain_call_macro<W: Write>(
        f: &mut W,
        func: &Function,
        macro_name: &str,
        callee: &str,
        hygienic: bool,
    ) -> io::Result<()> {
        let tokens = Self::c_macro_arg_tokens(
            func.function_args
                .iter()
                .filter(|arg| arg.vtype != VariableType::SelfType),
            hygienic,
        );
        if func.has_varargs {
            let params = tokens.join(", ");
            writeln!(
                f,
                "#define {}({}, ...) {}({}, __VA_ARGS__)",
                macro_name, params, callee, params
            )
        } else {
            writeln!(
                f,
                "#define {}({}) {}({})",
                macro_name,
                tokens.join(", "),
                callee,
                tokens.join(", ")
            )
        }
    }
}

/// Spell a cross-include for a referenced type's header. Some(prefix) →
/// `#include <prefix/module/stem.h>`; None → `#include "stem.h"` (same-dir, no
/// framework path).
fn cross_include(include_prefix: Option<&str>, module: &str, stem: &str) -> String {
    match include_prefix {
        Some(prefix) => format!("#include <{}/{}/{}.h>", prefix, module, stem),
        None => format!("#include \"{}.h\"", stem),
    }
}

/// A field plus its union-arm variants, if any. Dependency collection (includes,
/// forward-decls) must treat a type referenced only from inside a union arm the
/// same as one referenced by a plain field.
fn with_union_arms(var: &Variable) -> impl Iterator<Item = &Variable> + '_ {
    std::iter::once(var).chain(var.union_variants.iter().flatten())
}

fn api_value_iter(api_def: &ApiDef) -> impl Iterator<Item = &Variable> {
    api_def
        .apis
        .iter()
        .flat_map(|a| a.functions.iter())
        .flat_map(|func| func.function_args.iter().chain(func.return_val.iter()))
}

/// Every arg + return value across a def's struct function-fields (the vtable
/// case), folded into a header's include decisions exactly as api_value_iter is
/// for api-block prototypes. An extern opaque dep is not an authored type, so
/// it is absent from the cross-include map and stays forward-declared.
fn struct_fn_field_values(api_def: &ApiDef) -> impl Iterator<Item = &Variable> {
    api_def
        .structs
        .iter()
        .flat_map(|s| s.functions.iter())
        .flat_map(|func| func.function_args.iter().chain(func.return_val.iter()))
}

/// Every arg + return value across a def's `callback <Name>` typedefs.
fn callback_values(api_def: &ApiDef) -> impl Iterator<Item = &Variable> {
    api_def
        .callbacks
        .iter()
        .flat_map(|cb| cb.function_args.iter().chain(cb.return_val.iter()))
}

/// The trailing by-value config struct of an api slot, if any - the arg a
/// designated-initializer convenience macro builds from __VA_ARGS__. It is the
/// last non-self arg and must be a by-value generated struct:
/// VariableType::Regular, not a pointer, and not an array. A `callback <Name>`
/// arg is a named type too but a function-pointer typedef, not
/// designated-initializable, so it is excluded explicitly via is_callback.
fn convenience_config_arg(func: &Function) -> Option<&Variable> {
    let last = func
        .function_args
        .iter()
        .rev()
        .find(|a| a.vtype != VariableType::SelfType)?;
    let by_value_struct = last.vtype == VariableType::Regular
        && !last.is_callback
        && !last.pointer
        && !last.const_pointer
        && last.array.is_none();
    by_value_struct.then_some(last)
}

/// Whether a value is a fixed-width primitive (u32/i16/...) - it names a
/// stdint type. bool/char/void are primitives but not stdint types, and
/// usize/isize name `<stddef.h>` types (size_t/ptrdiff_t), not stdint.
fn is_fixed_width_primitive(v: &Variable) -> bool {
    v.vtype == VariableType::Primitive
        && v.type_name != "bool"
        && v.type_name != "char"
        && v.type_name != "void"
        && v.type_name != "usize"
        && v.type_name != "isize"
}

/// Whether a value names a `<stddef.h>` type - usize/isize map to
/// size_t/ptrdiff_t, which (unlike the fixed-width ints) live in `<stddef.h>`.
fn is_stddef_primitive(v: &Variable) -> bool {
    v.vtype == VariableType::Primitive && (v.type_name == "usize" || v.type_name == "isize")
}

/// Whether a value is bool - a primitive that names the `<stdbool.h>` type
/// (regardless of pointer-ness: a `bool*` out-param needs the include too).
fn is_bool_value(v: &Variable) -> bool {
    v.vtype == VariableType::Primitive && v.type_name == "bool"
}

fn is_string_value(v: &Variable) -> bool {
    v.vtype == VariableType::Str
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::{ApiDef, ApiParser};
    use std::process::Command;

    /// The first available system C compiler, or None (test skips).
    fn find_cc() -> Option<&'static str> {
        ["cc", "clang", "gcc"].into_iter().find(|cc| {
            Command::new(cc)
                .arg("--version")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
        })
    }

    /// Compile a standalone C TU and report whether it built. tag keeps the temp
    /// path unique per case so concurrent test threads don't clobber each other.
    fn compile_tu(cc: &str, tag: &str, tu: &str) -> bool {
        let dir = std::env::temp_dir();
        let src = dir.join(format!("api_gen_ac_{}_{}.c", std::process::id(), tag));
        let obj = dir.join(format!("api_gen_ac_{}_{}.o", std::process::id(), tag));
        std::fs::write(&src, tu).expect("write temp C");
        // The generated prototypes carry the FL_API export annotation (resolved via
        // <flowi/fl_api.h> in a real build); define it away for the isolated TU.
        let status = Command::new(cc)
            .args(["-c", "-x", "c", "-DFL_API="])
            .arg(&src)
            .arg("-o")
            .arg(&obj)
            .status()
            .expect("run cc");
        let _ = std::fs::remove_file(&src);
        let _ = std::fs::remove_file(&obj);
        status.success()
    }

    fn real_cursor_typedefs() -> String {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "enum CursorShape { Arrow = 0, Hand = 1, Text = 6, }\n\
             #[attributes(Copy)]\n\
             struct Cursor { shape: CursorShape }",
            "cursor.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for e in api_def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum emit");
        }
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct emit");
        }
        String::from_utf8(buf).expect("utf8 typedefs")
    }

    #[test]
    fn mod_emits_public_header_include_and_compiles_standalone() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(render)]\n\
             mod render_ir\n\
             struct Backend { frame: *RenderFrame }",
            "backend.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        // The include root is `<...>/flowi/include/flowi`, so the emitted
        // `<flowi/render/...>` resolves with `-I <...>/flowi/include`.
        let base = std::env::temp_dir().join(format!("api_gen_mod_{}", std::process::id()));
        let include_dir = base.join("flowi/include");
        let flowi_root = include_dir.join("flowi");
        let render_dir = flowi_root.join("render");
        std::fs::create_dir_all(&render_dir).expect("mk render dir");
        std::fs::write(
            render_dir.join("render_ir.h"),
            "#pragma once\ntypedef struct FlRenderFrame { int n; } FlRenderFrame;\n",
        )
        .expect("write render_ir.h");

        Cgen::generate_header(
            flowi_root.to_str().unwrap(),
            &api_def,
            &BTreeMap::new(),
            &crate::naming::FL,
            Some("flowi"),
            false,
            None,
            "scripts/gen.sh",
        )
        .expect("generate header");

        let header = std::fs::read_to_string(render_dir.join("backend.h")).expect("read backend.h");
        assert!(
            header.contains("#include <flowi/render/render_ir.h>"),
            "mod emits the public-header include against the def's module root"
        );
        assert!(
            header.contains("FlRenderFrame* frame;"),
            "the payload field is named by pointer through the normal Fl-prefix path"
        );

        if let Some(cc) = find_cc() {
            let tu = "#include <flowi/render/backend.h>\nint use_be(FlBackend* b) { return b->frame->n; }\n";
            let src = base.join("use_backend.c");
            std::fs::write(&src, tu).expect("write TU");
            let obj = base.join("use_backend.o");
            let status = Command::new(cc)
                .args(["-c", "-x", "c"])
                .arg(&src)
                .arg("-I")
                .arg(&include_dir)
                .arg("-o")
                .arg(&obj)
                .status()
                .expect("run cc");
            assert!(
                status.success(),
                "generated header must compile through the cross-include path"
            );
        } else {
            eprintln!("mod include compile test skipped: no cc/clang/gcc on PATH");
        }

        let _ = std::fs::remove_dir_all(&base);
    }

    #[test]
    fn real_type_header_compiles_and_uses_em_prefix() {
        let typedefs = real_cursor_typedefs();

        assert!(
            typedefs.contains("typedef enum FlCursorShape {"),
            "enum uses the Em prefix"
        );
        assert!(
            typedefs.contains("FlCursorShape_Arrow = 0,"),
            "enumerator uses the Em prefix"
        );
        assert!(
            typedefs.contains("typedef struct FlCursor {"),
            "struct uses the Em prefix"
        );
        assert!(
            typedefs.contains("FlCursorShape shape;"),
            "field type is the generated enum"
        );
        assert!(
            !typedefs.contains("_Static_assert"),
            "a real type has no drift guard"
        );

        let Some(cc) = find_cc() else {
            eprintln!("real-type compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "{}\nint use_cursor(void) {{ FlCursor c = {{ .shape = FlCursorShape_Text }}; return (int)c.shape; }}\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "real_header", &tu),
            "generated real typedefs must compile and be usable"
        );
    }

    /// A struct with an inline union field emits the union members inline -
    /// ABI-identical to the Rust side's named union type.
    #[test]
    fn real_type_struct_emits_inline_union_field() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(Copy)]\n\
             struct SizingMinMax { min: f32, max: f32 }\n\
             #[attributes(Copy)]\n\
             struct SizingAxis { size: union { min_max: SizingMinMax, percent: f32 }, tag: u32 }",
            "sizing.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("union {"),
            "union field emits an inline union"
        );
        assert!(
            typedefs.contains("FlSizingMinMax min_max;"),
            "union member uses the generated type"
        );
        assert!(
            typedefs.contains("float percent;"),
            "primitive union member spelled via stdint"
        );
        assert!(
            typedefs.contains("} size;"),
            "the inline union is named by the field"
        );
        assert!(
            !typedefs.contains("Em size;"),
            "no bare-prefix placeholder for the union field"
        );

        let Some(cc) = find_cc() else {
            eprintln!("inline-union compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\nint use_axis(void) {{ FlSizingAxis a = {{ .size = {{ .percent = 0.5f }}, .tag = 2 }}; return (int)a.size.percent; }}\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "inline_union", &tu),
            "generated inline-union struct must compile and be usable"
        );
    }

    /// A union field with the member name omitted emits a C11 anonymous union
    /// member (};) whose arms are reached directly off the struct (ev.move_.x).
    #[test]
    fn real_type_struct_emits_anonymous_union_member() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(Copy)]\n\
             struct MoveData { x: f32, y: f32 }\n\
             #[attributes(Copy)]\n\
             struct WheelData { x: f32, y: f32 }\n\
             #[attributes(Copy)]\n\
             struct PtrEvent { union { move_: MoveData, wheel: WheelData }, stamp: u64 }",
            "ptr.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("union {"),
            "anonymous union field emits an inline union"
        );
        assert!(
            typedefs.contains("    };"),
            "an unnamed union member closes with no field name"
        );
        assert!(
            !typedefs.contains("} ;"),
            "no stray empty field name after the union"
        );

        let Some(cc) = find_cc() else {
            eprintln!("anonymous-union compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\nint use_ev(void) {{ FlPtrEvent e = {{ .move_ = {{ .x = 1.0f }}, .stamp = 3 }}; return (int)e.move_.x + (int)e.wheel.y; }}\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "anon_union", &tu),
            "generated anonymous-union struct must compile with direct arm access"
        );
    }

    /// `#[enumerators(Stem)]` lets the type name and the constant prefix diverge
    /// (FlPtrEventType the type, FlPtrEvent_Move the constants).
    #[test]
    fn enumerators_attribute_overrides_constant_prefix() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[enumerators(PtrEvent)]\n\
             enum PtrEventType { Move = 0, Wheel = 1, }",
            "ptr.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for e in api_def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("typedef enum FlPtrEventType {"),
            "type name keeps the enum name"
        );
        assert!(
            typedefs.contains("FlPtrEvent_Move = 0,"),
            "constants use the override stem, not the type name"
        );
        assert!(
            !typedefs.contains("FlPtrEventType_Move"),
            "the type-name stem is replaced by the override"
        );

        let Some(cc) = find_cc() else {
            eprintln!("enumerator-override compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "{}\n_Static_assert(FlPtrEvent_Wheel == 1, \"override stem constant\");\nFlPtrEventType use_kind(void) {{ return FlPtrEvent_Move; }}\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "enum_override", &tu),
            "generated override enum must compile and be usable"
        );
    }

    #[test]
    fn or_list_enumerator_emits_combined_value() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(bitflags)]\n\
             enum Flags { None = 0, A = 1, B = 2, C = 4, AB = A | B, ABC = AB | C, }",
            "flags.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for e in api_def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("FlFlags_A = 1,"),
            "plain-valued entries are unaffected: {typedefs}"
        );
        assert!(
            typedefs.contains("FlFlags_AB = 3,"),
            "the or-list entry emits its combined value, not dropped: {typedefs}"
        );
        assert!(
            typedefs.contains("FlFlags_ABC = 7,"),
            "a nested or-list resolves through the referenced or-list: {typedefs}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("or-list compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "{}\n_Static_assert(FlFlags_AB == (FlFlags_A | FlFlags_B), \"or-list value\");\n\
             _Static_assert(FlFlags_ABC == (FlFlags_A | FlFlags_B | FlFlags_C), \"nested or-list\");\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "enum_or_list", &tu),
            "generated or-list enum must compile and hold the OR'd value"
        );
    }

    #[test]
    fn or_list_undefined_reference_errors() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(bitflags)]\n\
             enum Flags { A = 1, All = A | Missing, }",
            "flags.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        let res = Cgen::generate_enum(&mut buf, &api_def.enums[0], &crate::naming::FL);
        assert!(
            res.is_err(),
            "an undefined or-list reference must fail generation, got: {:?}",
            String::from_utf8(buf)
        );
        let msg = res.unwrap_err().to_string();
        assert!(
            msg.contains("Missing") && msg.contains("undefined"),
            "the error names the undefined enumerator: {msg}"
        );
    }

    /// The resolver's visiting guard: a cycle must terminate, not recurse forever.
    #[test]
    fn or_list_cyclic_reference_errors() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(bitflags)]\n\
             enum Flags { A = 1, All = A | All, }",
            "flags.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        let res = Cgen::generate_enum(&mut buf, &api_def.enums[0], &crate::naming::FL);
        assert!(
            res.is_err(),
            "a cyclic or-list reference must fail generation, got: {:?}",
            String::from_utf8(buf)
        );
        let msg = res.unwrap_err().to_string();
        assert!(
            msg.contains("cyclic") && msg.contains("All"),
            "the error reports the cycle and names the enumerator: {msg}"
        );
    }

    #[test]
    fn real_type_struct_emits_named_and_anonymous_union() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(Copy)]\n\
             struct ArmA { p: f32, q: f32 }\n\
             #[attributes(Copy)]\n\
             struct ArmB { r: f32, s: f32 }\n\
             #[attributes(Copy)]\n\
             struct Mixed { sel: union { a: ArmA, n: u32 }, union { b: ArmB, m: u32 }, tail: u64 }",
            "mixed.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("} sel;"),
            "the named union keeps its member name"
        );
        assert!(
            typedefs.contains("    };"),
            "the anonymous union closes with no member name"
        );

        let Some(cc) = find_cc() else {
            eprintln!("mixed-union compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\nint use_mixed(void) {{ FlMixed x = {{ .sel = {{ .n = 1 }}, .b = {{ .r = 2.0f }}, .tail = 3 }}; return (int)x.sel.a.p + (int)x.b.r; }}\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "mixed_union", &tu),
            "generated mixed-union struct must compile and be usable"
        );
    }

    #[test]
    fn real_type_packed_enum_emits_packed_attribute() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[attributes(packed)]\n\
             enum Dir { LeftToRight = 0, TopToBottom = 1, }",
            "dir.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let mut buf = Vec::new();
        for e in api_def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum emit");
        }
        let typedefs = String::from_utf8(buf).expect("utf8 typedefs");

        assert!(
            typedefs.contains("typedef enum __attribute__((__packed__)) FlDir {"),
            "packed enum emits the packed attribute"
        );

        let Some(cc) = find_cc() else {
            eprintln!("packed-enum compile test skipped: no cc/clang/gcc on PATH");
            return;
        };
        let tu = format!(
            "{}\n_Static_assert(sizeof(FlDir) == 1, \"packed enum is 1 byte\");\n",
            typedefs
        );
        assert!(
            compile_tu(cc, "packed_enum", &tu),
            "generated packed enum must compile and be 1 byte"
        );
    }

    /// Pinning string_type/string_include spells the IDL String base type as a
    /// foreign type and pulls its real header; an unpinned profile keeps the
    /// prefixed default.
    #[test]
    fn pinned_string_type_spells_the_foreign_string() {
        let api_def = parse_one(
            "#[attributes(service)] api Settings {\n\
                 rp_settings_probe(module_name: String) -> i32\n\
             }",
            "settings.def",
        );
        let mut rp = crate::naming::Naming::new("Rp", "rp");
        rp.string_type = Some(std::borrow::Cow::Borrowed("FlString"));
        rp.string_include = Some(std::borrow::Cow::Borrowed("flowi/core/string.h"));

        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &rp).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("RP_API int32_t rp_settings_probe(FlString module_name);"),
            "pinned string spelling + profile API macro reach the prototype: {out}"
        );

        let dir = std::env::temp_dir().join("api_gen_string_pin_test");
        std::fs::create_dir_all(&dir).expect("tmp dir");
        Cgen::generate_header(
            dir.to_str().expect("utf8 path"),
            &api_def,
            &BTreeMap::new(),
            &rp,
            Some("replay"),
            false,
            None,
            "scripts/gen.sh",
        )
        .expect("header");
        let header = std::fs::read_to_string(dir.join(api_def.module.as_str()).join("settings.h"))
            .expect("read header");
        assert!(
            header.contains("#include <flowi/core/string.h>"),
            "pinned include wins over the derived <replay/core/string.h>: {header}"
        );
        assert!(
            !header.contains("RpString"),
            "no RpString anywhere: {header}"
        );
        assert!(
            header.contains("#include <replay/rp_api.h>"),
            "the API-macro include follows the profile: {header}"
        );
    }

    fn parse_one(defs: &str, file: &str) -> ApiDef {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(defs, file, &mut api_def);
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        api_def
    }

    #[test]
    fn opaque_type_emits_forward_decl_only_and_compiles() {
        let api_def = parse_one(
            "#[attributes(Opaque)]\nstruct TextInputState {}",
            "text_input.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "TextInputState")
            .expect("parsed");
        assert!(sdef.is_opaque(), "the Opaque attribute marks it opaque");
        assert!(
            sdef.emits_typedef_header(),
            "an opaque type emits a header decl"
        );

        let mut buf = Vec::new();
        Cgen::generate_opaque_forward_decl(&mut buf, sdef, &crate::naming::FL)
            .expect("opaque emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("typedef struct FlTextInputState FlTextInputState;"),
            "opaque emits a forward-declaration spelled by the Em profile"
        );
        assert!(
            !out.contains('{'),
            "an opaque forward-decl has no struct body"
        );

        let Some(cc) = find_cc() else {
            eprintln!("opaque compile test skipped: no cc on PATH");
            return;
        };
        // Usable behind a pointer with no definition in scope.
        let tu = format!(
            "{}\nint use_it(FlTextInputState* p) {{ return p != (void*)0; }}\n",
            out
        );
        assert!(
            compile_tu(cc, "opaque", &tu),
            "the forward-decl must compile and support pointer use"
        );
    }

    #[test]
    fn recursive_structs_emit_forward_decls_and_compile() {
        // Elem.next is a self-ref; Elem.value forward-refs Val (defined after Elem).
        let api_def = parse_one(
            "struct Elem { value: *Val, next: *Elem }\n\
             struct Val { payload: *void, kind: usize }",
            "recur.def",
        );
        let needed = Cgen::structs_needing_forward_decl(&api_def);
        assert!(
            needed.contains("Elem"),
            "the self-referencing Elem needs a forward-decl"
        );
        assert!(
            needed.contains("Val"),
            "Val is forward-referenced by Elem, so it needs one too"
        );
        assert_eq!(
            needed.len(),
            2,
            "only the two recursively-referenced structs are forward-declared"
        );

        let plain = parse_one("struct Plain { x: i32, y: i32 }", "plain.def");
        assert!(
            Cgen::structs_needing_forward_decl(&plain).is_empty(),
            "a struct with no self/forward struct-pointer field gets no forward-decl"
        );

        let mut buf = Vec::new();
        for sdef in api_def
            .structs
            .iter()
            .filter(|s| needed.contains(s.name.as_str()))
        {
            Cgen::generate_struct_forward_decl(&mut buf, sdef, &crate::naming::FL)
                .expect("fwd emit");
        }
        for sdef in &api_def.structs {
            Cgen::generate_struct(&mut buf, sdef, &crate::naming::FL).expect("body emit");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("typedef struct FlElem FlElem;"),
            "Elem forward-decl emitted"
        );
        assert!(
            out.contains("typedef struct FlVal FlVal;"),
            "Val forward-decl emitted"
        );
        assert!(
            out.contains("FlVal* value;"),
            "the forward-ref field names the typedef"
        );
        assert!(
            out.contains("FlElem* next;"),
            "the self-ref field names the typedef"
        );

        let Some(cc) = find_cc() else {
            eprintln!("recursive struct compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stddef.h>\n{}\nint use_it(FlElem* e) {{ return e->next != (void*)0; }}\n",
            out
        );
        assert!(
            compile_tu(cc, "recursive", &tu),
            "the forward-decls + bodies must compile"
        );
    }

    #[test]
    fn union_arm_only_reference_pulls_dep_include() {
        let api_def = parse_one(
            "struct Holder { tag: u32, payload: union { c: Color, n: u32 } }",
            "holder.def",
        );
        let mut type_loc: BTreeMap<String, (String, String)> = BTreeMap::new();
        type_loc.insert(
            "Color".to_owned(),
            ("core".to_owned(), "math_data".to_owned()),
        );
        let includes = Cgen::header_dep_includes(&api_def, &type_loc, Some("flowi"));
        assert_eq!(
            includes,
            vec!["#include <flowi/core/math_data.h>".to_owned()],
            "a union-arm-only Color reference pulls math_data.h"
        );

        let plain = parse_one(
            "struct Plain { payload: union { a: u32, b: f32 }, tag: u32 }",
            "plain.def",
        );
        assert!(
            Cgen::header_dep_includes(&plain, &type_loc, Some("flowi")).is_empty(),
            "primitive-only union arms pull no include"
        );
    }

    #[test]
    fn union_arm_pointer_ref_needs_forward_decl_and_compiles() {
        // next is a self-ref, val forward-refs Late - both live only in the union.
        let api_def = parse_one(
            "struct Node { link: union { next: *Node, val: *Late }, tag: u32 }\n\
             struct Late { x: i32 }",
            "node.def",
        );
        let needed = Cgen::structs_needing_forward_decl(&api_def);
        assert!(
            needed.contains("Node"),
            "the union-arm self-ref marks Node as needing a forward-decl"
        );
        assert!(
            needed.contains("Late"),
            "the union-arm forward-ref marks Late as needing a forward-decl"
        );
        assert_eq!(
            needed.len(),
            2,
            "only the two referenced structs are marked"
        );

        let mut buf = Vec::new();
        for sdef in api_def
            .structs
            .iter()
            .filter(|s| needed.contains(s.name.as_str()))
        {
            Cgen::generate_struct_forward_decl(&mut buf, sdef, &crate::naming::FL)
                .expect("fwd emit");
        }
        for sdef in &api_def.structs {
            Cgen::generate_struct(&mut buf, sdef, &crate::naming::FL).expect("body emit");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("typedef struct FlNode FlNode;"),
            "Node forward-decl emitted"
        );
        assert!(
            out.contains("typedef struct FlLate FlLate;"),
            "Late forward-decl emitted"
        );

        let Some(cc) = find_cc() else {
            eprintln!("union-arm forward-decl compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\nint use_it(FlNode* n) {{ return n->link.next != (void*)0; }}\n",
            out
        );
        assert!(
            compile_tu(cc, "union_arm_fwd", &tu),
            "the union-arm forward-decls + bodies must compile"
        );
    }

    #[test]
    fn handle_emits_typedef_and_sentinel_and_compiles() {
        let api_def = parse_one(
            "#[handle(u32, invalid = 0xFFFFFFFF)]\nstruct ImageHandle {}",
            "image_handle.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "ImageHandle")
            .expect("parsed");
        assert!(sdef.is_handle_type, "#[handle(...)] marks a handle");

        let mut buf = Vec::new();
        Cgen::generate_handle_typedef(&mut buf, sdef, &crate::naming::FL).expect("handle emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("typedef uint32_t FlImageHandle;"),
            "handle typedefs its underlying width"
        );
        assert!(
            out.contains("#define FL_IMAGE_HANDLE_INVALID 0xFFFFFFFF"),
            "handle emits its invalid sentinel define"
        );

        let Some(cc) = find_cc() else {
            eprintln!("handle compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\nint invalid(FlImageHandle h) {{ return h == FL_IMAGE_HANDLE_INVALID; }}\n",
            out
        );
        assert!(
            compile_tu(cc, "handle", &tu),
            "the handle typedef + sentinel must compile and be usable"
        );
    }

    #[test]
    fn pointer_primitive_fields_emit_and_compile() {
        let api_def = parse_one(
            "struct Span { text: *const char, blob: *const void, scratch: *void }",
            "span.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "Span")
            .expect("parsed");

        let mut buf = Vec::new();
        Cgen::generate_struct(&mut buf, sdef, &crate::naming::FL).expect("struct emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(out.contains("const char* text;"), "const char* field");
        assert!(out.contains("const void* blob;"), "const void* field");
        assert!(out.contains("void* scratch;"), "void* field");

        let Some(cc) = find_cc() else {
            eprintln!("pointer-primitive compile test skipped: no cc on PATH");
            return;
        };
        assert!(
            compile_tu(cc, "ptr_prims", &out),
            "a struct with pointer-primitive fields must compile"
        );
    }

    /// The size suffix belongs on the declarator, not the type.
    #[test]
    fn fixed_array_field_emits_and_compiles() {
        let api_def = parse_one(
            "struct Cell { name: [u8; 24], scope_width: u8 }",
            "cell.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "Cell")
            .expect("parsed");

        let mut buf = Vec::new();
        Cgen::generate_struct(&mut buf, sdef, &crate::naming::FL).expect("struct emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("uint8_t name[24];"),
            "fixed array field: {}",
            out
        );
        assert!(
            out.contains("uint8_t scope_width;"),
            "trailing scalar field"
        );

        let Some(cc) = find_cc() else {
            eprintln!("fixed-array compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdint.h>\n{}\n_Static_assert(sizeof(FlCell) == 25, \"cell size\");\n",
            out
        );
        assert!(
            compile_tu(cc, "fixed_array", &tu),
            "fixed-array struct must compile"
        );
    }

    /// A referenced `#[attributes(Opaque)]` type is profile-named like every other
    /// type - there is no verbatim "external" path - and never re-laid-out.
    #[test]
    fn referenced_opaque_type_is_profile_named() {
        let api_def = parse_one(
            "#[attributes(Opaque)]\nstruct Arena {}\nstruct Ctx { arena: *Arena }",
            "ctx.def",
        );
        let sdef = api_def
            .structs
            .iter()
            .find(|s| s.name == "Ctx")
            .expect("parsed");

        let mut buf = Vec::new();
        Cgen::generate_struct(&mut buf, sdef, &crate::naming::FL).expect("struct emit");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("FlArena* arena;"),
            "the referenced opaque type is profile-named"
        );
        assert!(!out.contains("RpArena"), "no verbatim Rp spelling survives");
        assert!(
            !out.contains("typedef struct FlArena"),
            "an opaque field reference never (re)defines the type"
        );

        let Some(cc) = find_cc() else {
            eprintln!("opaque-reference compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!("typedef struct FlArena FlArena;\n{}", out);
        assert!(
            compile_tu(cc, "opaque_ref", &tu),
            "the reference must compile against the forward decl"
        );
    }

    #[test]
    fn struct_function_fields_and_extern_opaque_emit_and_compile() {
        let api_def = parse_one(
            "extern opaque UiCtx\n\
             extern opaque FlArena\n\
             enum Device { Keyboard, Mouse }\n\
             struct Backend {\n\
                 ctx: *void,\n\
                 destroy(ctx: *void),\n\
                 poll(ctx: *void, ui: *UiCtx) -> bool,\n\
                 clip(ctx: *void, arena: *FlArena) -> String,\n\
                 rumble(ctx: *void, index: i32, power: f32),\n\
                 last(ctx: *void) -> Device,\n\
                 on_job: bool,\n\
             }",
            "backend.def",
        );

        let mut buf = Vec::new();
        for ext in &api_def.externs {
            Cgen::generate_extern_opaque_forward_decl(&mut buf, ext).expect("extern emit");
        }
        for e in api_def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum emit");
        }
        for s in api_def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct emit");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("typedef struct UiCtx UiCtx;"),
            "UiCtx forward-decl verbatim"
        );
        assert!(
            out.contains("typedef struct FlArena FlArena;"),
            "FlArena forward-decl verbatim"
        );
        assert!(
            !out.contains("FlUiCtx"),
            "extern-opaque name is not Fl-prefixed"
        );
        assert!(out.contains("void (*destroy)(void* ctx);"), "void fn-field");
        assert!(
            out.contains("bool (*poll)(void* ctx, UiCtx* ui);"),
            "extern-opaque ptr arg"
        );
        assert!(
            out.contains("FlString (*clip)(void* ctx, FlArena* arena);"),
            "by-value FlString return"
        );
        assert!(
            out.contains("void (*rumble)(void* ctx, int32_t index, float power);"),
            "fixed-width args"
        );
        assert!(
            out.contains("FlDevice (*last)(void* ctx);"),
            "generated enum return is Fl-prefixed"
        );
        // Authored order is preserved: the trailing on_job value field is emitted
        // AFTER the function-pointer members, not hoisted ahead of them.
        assert!(
            out.contains("bool on_job;"),
            "trailing value field emitted: {out}"
        );
        assert!(
            out.find("bool on_job;") > out.find("(*last)"),
            "trailing value field emitted after the fn-fields: {out}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("vtable compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdbool.h>\n#include <stdint.h>\n\
             typedef struct FlString {{ const char* p; long n; }} FlString;\n\
             {out}\n\
             struct UiCtx {{ int x; }};\n\
             static bool poll_impl(void* ctx, UiCtx* ui) {{ (void)ctx; (void)ui; return true; }}\n\
             int use_backend(void) {{\n\
                 FlBackend b = {{ 0 }};\n\
                 b.poll = poll_impl;\n\
                 return b.poll ? (int)b.poll(b.ctx, (UiCtx*)0) : 0;\n\
             }}\n",
            out = out,
        );
        assert!(
            compile_tu(cc, "vtable", &tu),
            "the generated vtable + forward-decls must compile and be callable"
        );
    }

    /// The emitted typedef must be byte-identical to the hand-written
    /// FlVfsListingCallback, which the abi-check TU enforces at the C level.
    #[test]
    fn callback_emits_typedef_byte_identical_and_compiles() {
        let api_def = parse_one(
            "extern opaque FlVfsEntry\n\
             callback VfsListingCallback(user_data: *void, entry: *const FlVfsEntry) -> bool",
            "vfs_listing.def",
        );
        let cb = api_def
            .callbacks
            .iter()
            .find(|c| c.name == "VfsListingCallback")
            .expect("parsed");

        let mut buf = Vec::new();
        Cgen::generate_callback_typedef(&mut buf, cb, &crate::naming::FL).expect("callback emit");
        let out = String::from_utf8(buf).expect("utf8");

        const HAND_WRITTEN: &str =
            "typedef bool (*FlVfsListingCallback)(void* user_data, const FlVfsEntry* entry);";
        assert!(
            out.lines().any(|l| l == HAND_WRITTEN),
            "generated typedef must be byte-identical to the hand-written one:\n{out}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("callback compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdbool.h>\n\
             typedef struct FlVfsEntry FlVfsEntry;\n\
             {out}\n\
             static bool probe(void* u, const FlVfsEntry* e) {{ (void)u; (void)e; return true; }}\n\
             int use_cb(void) {{ FlVfsListingCallback cb = probe; return cb ? (int)cb((void*)0, (const FlVfsEntry*)0) : 0; }}\n",
            out = out,
        );
        assert!(
            compile_tu(cc, "callback", &tu),
            "the generated callback typedef must compile and be usable"
        );
    }

    #[test]
    fn callback_usable_as_field_and_arg_compiles() {
        let api_def = parse_one(
            "callback Sink(value: i32) -> bool\n\
             struct Pipe { on_value: Sink, tag: u32 }\n\
             api Stream { connect(sink: Sink) }",
            "stream.def",
        );

        let cb = &api_def.callbacks[0];
        let pipe = api_def
            .structs
            .iter()
            .find(|s| s.name == "Pipe")
            .expect("struct");

        let mut buf = Vec::new();
        Cgen::generate_callback_typedef(&mut buf, cb, &crate::naming::FL).expect("callback");
        Cgen::generate_struct(&mut buf, pipe, &crate::naming::FL).expect("struct");
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("FlSink on_value;"),
            "callback as a struct field: {out}"
        );
        assert!(
            out.contains("void fl_stream_connect(FlSink sink);"),
            "callback as an api arg: {out}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("callback field/arg compile test skipped: no cc on PATH");
            return;
        };
        let tu = format!(
            "#include <stdbool.h>\n#include <stdint.h>\n\
             {out}\n\
             static bool probe(int32_t v) {{ return v != 0; }}\n\
             void fl_stream_connect(FlSink sink) {{ (void)sink; }}\n\
             int use_it(void) {{ FlPipe p = {{ probe, 7 }}; fl_stream_connect(p.on_value); return p.on_value ? (int)p.on_value(1) : 0; }}\n",
            out = out,
        );
        assert!(
            compile_tu(cc, "callback_field_arg", &tu),
            "callback field + arg must compile and be usable"
        );
    }

    /// An `[array(T, N)]` marker does not change the C surface: the prototype keeps
    /// the plain `const uint8_t*` the def's `*const u8` spells.
    #[test]
    fn array_marked_arg_keeps_plain_const_pointer_in_c() {
        let api_def = parse_one(
            "#[attributes(service)]\n\
             api Hash { hash_lookup([array(u8, 16)] md5: *const u8, subsong: u16) -> u32 }",
            "hash.def",
        );
        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("uint32_t hash_lookup(const uint8_t* md5, uint16_t subsong);"),
            "C prototype unchanged by the marker: {out}"
        );
    }

    /// A `callback <Name>` arg in the trailing api-fn position is a named type but a
    /// function-pointer typedef, not a designated-initializable by-value config
    /// struct, so it must NOT trigger a convenience macro.
    #[test]
    fn trailing_callback_arg_gets_no_convenience_macro() {
        let api_def = parse_one(
            "callback FrameFn(user_data: *void)\n\
             api Runner { run(user_data: *void, frame: FrameFn) }",
            "runner.def",
        );

        let frame = api_def.apis[0].functions[0]
            .function_args
            .last()
            .expect("trailing arg");
        assert!(
            frame.is_callback,
            "the trailing callback arg is flagged is_callback"
        );
        assert!(
            convenience_config_arg(&api_def.apis[0].functions[0]).is_none(),
            "callback arg is not a config slot"
        );

        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("void fl_runner_run(void* user_data, FlFrameFn frame);"),
            "prototype: {out}"
        );
        assert!(
            !out.contains("#define FL_RUNNER_RUN"),
            "a trailing callback arg gets no convenience macro: {out}"
        );
        assert!(
            !out.contains("{ __VA_ARGS__ }"),
            "no designated-init literal for a function-pointer arg: {out}"
        );
    }

    /// The is_callback exclusion keys off the trailing arg only, so it must not
    /// over-suppress.
    #[test]
    fn non_trailing_callback_keeps_config_macro() {
        let api_def = parse_one(
            "callback FrameFn(user_data: *void)\n\
             struct Opts { flags: u32 }\n\
             api Runner { on(frame: FrameFn, opts: Opts) }",
            "runner.def",
        );

        let func = &api_def.apis[0].functions[0];
        assert!(
            func.function_args[0].is_callback,
            "the non-trailing callback arg is flagged"
        );
        let cfg =
            convenience_config_arg(func).expect("trailing by-value struct is still a config slot");
        assert_eq!(
            cfg.name, "opts",
            "the trailing struct, not the callback, is the config arg"
        );

        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains(
                "#define fl_runner_on(frame, ...) fl_runner_on(frame, (FlOpts) { __VA_ARGS__ })"
            ),
            "direct convenience wrapper stays lowercase: {out}"
        );
    }

    /// A `[scope_end]` slot takes a whole mark struct by value and is always called
    /// with an existing mark variable, so a designated-init convenience macro would
    /// rewrite arena_temp_end(mark) into arena_temp_end((FlTempArena){ mark }).
    #[test]
    fn scope_end_whole_struct_slot_gets_no_convenience_macro() {
        let api_def = parse_one(
            "#[attributes(Opaque)] struct Arena {}\n\
             struct TempArena { arena: *Arena, pos: u64 }\n\
             #[attributes(service)] api Arena {\n\
                 [scope_begin] arena_temp_begin(arena: *Arena) -> TempArena\n\
                 [scope_end] arena_temp_end(temp: TempArena)\n\
             }",
            "arena.def",
        );

        let end = &api_def.apis[0].functions[1];
        assert!(end.is_scope_end, "the slot parses as [scope_end]");
        assert!(
            convenience_config_arg(end).is_some(),
            "its whole-struct-by-value arg would otherwise be treated as a config slot"
        );

        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("FL_API void arena_temp_end(FlTempArena temp);"),
            "the scope-end slot emits its bare FL_API prototype: {out}"
        );
        assert!(
            !out.contains("#define arena_temp_end"),
            "a [scope_end] slot emits no convenience macro that would shadow it: {out}"
        );
        assert!(
            !out.contains("arena_temp_end_impl"),
            "a [scope_end] slot emits no `_impl` companion: {out}"
        );
    }

    /// The !api.is_service half of the convenience-macro suppression, which
    /// scope_end_whole_struct_slot_gets_no_convenience_macro does not pin (its slot
    /// is BOTH is_service AND is_scope_end). The identical slot in a non-service
    /// block still gets the macro, so the gate is the service attribute, not the
    /// whole-struct arg shape.
    #[test]
    fn service_whole_struct_slot_suppresses_macro_but_non_service_keeps_it() {
        let service = parse_one(
            "struct StringBuilder { data: *void, len: u64 }\n\
             #[attributes(service)] api String {\n\
                 sb_clear(sb: StringBuilder) -> StringBuilder\n\
             }",
            "string.def",
        );
        let clear = &service.apis[0].functions[0];
        assert!(!clear.is_scope_end, "the control slot is NOT [scope_end]");
        assert!(
            convenience_config_arg(clear).is_some(),
            "its whole-struct-by-value arg would otherwise be treated as a config slot"
        );

        let mut buf = Vec::new();
        for api in &service.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let svc_out = String::from_utf8(buf).expect("utf8");
        assert!(
            svc_out.contains("FL_API FlStringBuilder sb_clear(FlStringBuilder sb);"),
            "the service slot emits its bare raw-name prototype: {svc_out}"
        );
        assert!(
            !svc_out.contains("#define sb_clear"),
            "a service slot emits no designated-init convenience macro: {svc_out}"
        );

        let plain = parse_one(
            "struct StringBuilder { data: *void, len: u64 }\n\
             api String {\n\
                 sb_clear(sb: StringBuilder) -> StringBuilder\n\
             }",
            "string.def",
        );
        let mut buf2 = Vec::new();
        for api in &plain.apis {
            Cgen::generate_api_decls(&mut buf2, api, &crate::naming::FL).expect("api decls");
        }
        let plain_out = String::from_utf8(buf2).expect("utf8");
        assert!(
            plain_out.contains("#define fl_string_sb_clear("),
            "the same slot in a non-service block DOES get the convenience macro: {plain_out}"
        );
    }

    #[test]
    fn impl_slot_gets_a_lowercase_call_macro() {
        let api_def = parse_one(
            "struct Cfg { a: i32 }\n\
             api Menu { radio_impl(label: String, config: Cfg) -> bool\n\
                        set(value: Cfg) }",
            "menu.def",
        );

        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains(
                "#define fl_menu_radio(label, ...) fl_menu_radio_impl(label, (FlCfg) { __VA_ARGS__ })"
            ),
            "_impl slot emits a lowercase call macro: {out}"
        );
        assert!(
            !out.contains("FL_MENU_RADIO_IMPL"),
            "no SHOUTY _IMPL macro survives: {out}"
        );
        assert!(
            out.contains("#define fl_menu_set(...) fl_menu_set((FlCfg) { __VA_ARGS__ })"),
            "non-_impl direct wrapper is lowercase: {out}"
        );
    }

    /// A new primary slot emits the bare `fl_<block>` prototype (no slot word, no
    /// macro); a new_impl primary slot emits the `fl_<block>_impl` body plus the
    /// bare `fl_<block>` convenience macro; non-primary slots are unchanged.
    #[test]
    fn primary_slot_emits_the_bare_name() {
        // new slot, no config: bare prototype, no macro.
        let api_def = parse_one(
            "api Button { new(label: String) -> Signal\n\
                                  image(label: String) -> Signal }",
            "button.def",
        );
        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("fl_button(FlString label)"),
            "bare primary prototype: {out}"
        );
        assert!(
            out.contains("fl_button_image(FlString label)"),
            "non-primary unchanged: {out}"
        );

        // new_impl slot with a config struct: fl_button_impl body + bare fl_button macro.
        let api_def = parse_one(
            "struct Cfg { a: i32 }\n\
                                 api Button { new_impl(label: String, config: Cfg) -> Signal }",
            "button.def",
        );
        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("fl_button_impl(FlString label, FlCfg config)"),
            "impl body: {out}"
        );
        assert!(
            out.contains(
                "#define fl_button(label, ...) fl_button_impl(label, (FlCfg) { __VA_ARGS__ })"
            ),
            "bare convenience macro: {out}"
        );
    }

    /// The macro must take and forward the `<name>_size` companion too, so the size
    /// token is not swallowed by the trailing config struct.
    #[test]
    fn slice_arg_threads_size_companion_into_convenience_macro() {
        let api_def = parse_one(
            "struct Cfg { a: i32 }\n\
             api Tabs { new_impl(tabs: [*const String], selected: *i32, config: Cfg) -> bool }",
            "tabs.def",
        );
        let mut buf = Vec::new();
        for api in &api_def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        let out = String::from_utf8(buf).expect("utf8");
        assert!(
            out.contains("fl_tabs_impl(const FlString* tabs, uint32_t tabs_size, int32_t* selected, FlCfg config)"),
            "prototype expands slice to pointer + size: {out}"
        );
        assert!(
            out.contains(
                "#define fl_tabs(tabs, tabs_size, selected, ...) fl_tabs_impl(tabs, tabs_size, selected, (FlCfg) { __VA_ARGS__ })"
            ),
            "macro takes and forwards the size companion: {out}"
        );
    }

    // -------------------------------------------------------------------------
    // API construct.
    // -------------------------------------------------------------------------

    /// The cursor (types + api Cursor) and format (api Format, varargs) defs,
    /// parsed together so cross-file types resolve.
    fn api_defs_cursor_format() -> Vec<ApiDef> {
        let mut cursor = ApiDef::default();
        ApiParser::parse_string(
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
            &mut cursor,
        );
        let mut format = ApiDef::default();
        ApiParser::parse_string(
            "api Format { frame_string(fmt: *const char, ...) -> String }",
            "format.def",
            &mut format,
        );
        let mut defs = vec![cursor, format];
        ApiParser::second_pass(&mut defs, &crate::naming::FL);
        defs
    }

    /// The typedef-header section a domain emits: its real types (if any) then its
    /// api block declarations (direct `fl_*` prototypes + any call macro).
    fn header_section(def: &ApiDef) -> String {
        let mut buf = Vec::new();
        for e in def.enums.iter().filter(|e| e.is_real_type()) {
            Cgen::generate_enum(&mut buf, e, &crate::naming::FL).expect("enum");
        }
        for s in def.structs.iter().filter(|s| s.is_real_type()) {
            Cgen::generate_struct(&mut buf, s, &crate::naming::FL).expect("struct");
        }
        for api in &def.apis {
            Cgen::generate_api_decls(&mut buf, api, &crate::naming::FL).expect("api decls");
        }
        String::from_utf8(buf).expect("utf8")
    }

    /// The generated `fl_*` prototypes and call macros compile together and are
    /// callable directly (no vtable / no g_fl_ui), with the hand-written bodies
    /// linked in.
    #[test]
    fn api_direct_decls_compile_and_are_callable() {
        let defs = api_defs_cursor_format();

        let cursor_h = header_section(&defs[0]);
        assert!(
            cursor_h.contains("void fl_cursor_set(FlCursor cursor);"),
            "direct prototype"
        );
        assert!(
            cursor_h.contains("FlCursor fl_cursor_get_requested(void);"),
            "no-arg -> value"
        );
        assert!(
            cursor_h.contains("bool fl_cursor_get_visible(void);"),
            "bool-returning prototype"
        );
        assert!(
            !cursor_h.contains("FlCursorAPI"),
            "no fn-pointer vtable struct"
        );
        assert!(
            !cursor_h.contains("g_fl_cursor"),
            "no extern wiring instance"
        );
        assert!(!cursor_h.contains("g_fl_ui"), "no root-vtable routing");
        assert!(
            cursor_h
                .contains("#define fl_cursor_set(...) fl_cursor_set((FlCursor) { __VA_ARGS__ })"),
            "the direct cursor wrapper is lowercase"
        );
        assert!(
            !cursor_h.contains("FL_CURSOR_SET_VISIBLE"),
            "a primitive-arg slot gets no convenience macro"
        );

        let format_h = header_section(&defs[1]);
        assert!(
            format_h.contains("FlString fl_format_frame_string(const char* fmt, ...);"),
            "varargs prototype"
        );
        assert!(
            !format_h.contains("#define fl_format_frame_string"),
            "the direct varargs function has no wrapper macro"
        );

        let Some(cc) = find_cc() else {
            eprintln!("api direct compile test skipped: no cc on PATH");
            return;
        };

        let tu = format!(
            "#include <stdbool.h>\n\
             typedef struct FlString {{ const char* p; long n; }} FlString;\n\
             {cursor_h}\n{format_h}\n\
             void (fl_cursor_set)(FlCursor cursor) {{ (void)cursor; }}\n\
             FlCursor fl_cursor_get_requested(void) {{ FlCursor c = {{ FlCursorShape_Arrow }}; return c; }}\n\
             void fl_cursor_set_visible(bool visible) {{ (void)visible; }}\n\
             bool fl_cursor_get_visible(void) {{ return true; }}\n\
             FlString fl_format_frame_string(const char* fmt, ...) {{ (void)fmt; FlString s = {{ 0, 0 }}; return s; }}\n\
             int use_api(void) {{\n\
                 fl_cursor_set(.shape = FlCursorShape_Text);\n\
                 FlCursor c = fl_cursor_get_requested();\n\
                 fl_cursor_set_visible(fl_cursor_get_visible());\n\
                 FlString s = fl_format_frame_string(\"%d\", 1);\n\
                 return (int)c.shape + (int)s.n;\n\
             }}\n",
            cursor_h = cursor_h,
            format_h = format_h,
        );
        assert!(
            compile_tu(cc, "api_direct", &tu),
            "the generated direct prototypes + macros must compile and be callable"
        );
    }

    /// Signature drift between a hand-written body and the generated prototype is
    /// what the prototype exists to catch.
    #[test]
    fn api_body_signature_drift_fails_to_compile() {
        let Some(cc) = find_cc() else {
            eprintln!("api drift test skipped: no cc on PATH");
            return;
        };
        let defs = api_defs_cursor_format();
        let cursor_h = header_section(&defs[0]);

        let good = format!(
            "#include <stdbool.h>\n#define FL_API_IMPLEMENTATION\n{cursor_h}\nvoid fl_cursor_set(FlCursor cursor) {{ (void)cursor; }}\n",
            cursor_h = cursor_h
        );
        assert!(
            compile_tu(cc, "api_body_good", &good),
            "a matching body compiles"
        );

        // int where the prototype says FlCursor -> conflicting types.
        let bad = format!(
            "#include <stdbool.h>\n#define FL_API_IMPLEMENTATION\n{cursor_h}\nvoid fl_cursor_set(int cursor) {{ (void)cursor; }}\n",
            cursor_h = cursor_h
        );
        assert!(
            !compile_tu(cc, "api_body_bad", &bad),
            "a body whose signature drifts from the generated prototype must fail to compile"
        );
    }

    /// A callback typedef that names a generated struct by pointer is emitted
    /// ahead of every struct body, so the struct needs an up-front forward-decl -
    /// otherwise the function-pointer typedef names an undeclared type.
    #[test]
    fn callback_pointer_arg_forward_declares_its_struct_and_compiles() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(view)]\n\
             callback RenderItemFn(item: *const Item, focused: bool)\n\
             struct Item { id: u32 }\n\
             struct Options { render: RenderItemFn }",
            "view.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let dir = std::env::temp_dir().join(format!("api_gen_cbfwd_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("tmp dir");
        Cgen::generate_header(
            dir.to_str().expect("utf8 path"),
            &api_def,
            &BTreeMap::new(),
            &crate::naming::FL,
            Some("flowi"),
            false,
            None,
            "scripts/gen.sh",
        )
        .expect("header");
        let header = std::fs::read_to_string(dir.join("view").join("view.h")).expect("read view.h");
        let _ = std::fs::remove_dir_all(&dir);

        let fwd = "typedef struct FlItem FlItem;";
        let cb = "typedef void (*FlRenderItemFn)(const FlItem* item, bool focused);";
        assert!(header.contains(fwd), "forward-decl emitted: {header}");
        assert!(
            header.find(fwd) < header.find(cb),
            "forward-decl precedes the callback typedef: {header}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("callback forward-decl compile test skipped: no cc on PATH");
            return;
        };
        assert!(
            compile_tu(cc, "cb_fwd", &header),
            "the generated header compiles standalone: {header}"
        );
    }

    /// The same forward-decl need on a callback's return type, and the two
    /// kinds of pointer arg that must NOT be forward-declared: an extern
    /// opaque dep (already forward-declared by its own emitter, so a second
    /// typedef struct under the profile-prefixed name would be a different,
    /// bogus type) and another callback typedef.
    #[test]
    fn callback_return_forward_declares_but_opaque_and_callback_args_do_not() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(view)]\n\
             extern opaque UiCtx\n\
             callback SinkFn(value: u32)\n\
             callback ResolveFn(ctx: *UiCtx, sink: SinkFn) -> *const Resolved\n\
             struct Resolved { id: u32 }",
            "view.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);

        let dir = std::env::temp_dir().join(format!("api_gen_cbret_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("tmp dir");
        Cgen::generate_header(
            dir.to_str().expect("utf8 path"),
            &api_def,
            &BTreeMap::new(),
            &crate::naming::FL,
            Some("flowi"),
            false,
            None,
            "scripts/gen.sh",
        )
        .expect("header");
        let header = std::fs::read_to_string(dir.join("view").join("view.h")).expect("read view.h");
        let _ = std::fs::remove_dir_all(&dir);

        let fwd = "typedef struct FlResolved FlResolved;";
        let cb = "typedef const FlResolved* (*FlResolveFn)(UiCtx* ctx, FlSinkFn sink);";
        assert!(
            header.contains(fwd),
            "return type forward-declared: {header}"
        );
        assert!(
            header.find(fwd) < header.find(cb),
            "forward-decl precedes the callback typedef: {header}"
        );
        assert_eq!(
            header.matches("typedef struct UiCtx UiCtx;").count(),
            1,
            "opaque declared once, unprefixed: {header}"
        );
        assert!(
            !header.contains("FlUiCtx") && !header.contains("typedef struct FlSinkFn"),
            "no bogus forward-decl for an opaque or callback arg: {header}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("callback return forward-decl compile test skipped: no cc on PATH");
            return;
        };
        assert!(
            compile_tu(cc, "cb_ret", &header),
            "the generated header compiles standalone: {header}"
        );
    }

    /// static_assert on each struct's size and every field offset, pinning
    /// api_gen's LP64 model to what the compiler actually lays out. Opt-in.
    #[test]
    fn c_layout_asserts_pin_size_and_offsets_and_compile() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(pin)]\n\
             struct Entry { flag: bool, count: u32, total: u64 }",
            "pin.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let defs = vec![api_def];
        let registry = crate::layout::TypeRegistry::build(&defs);

        let dir = std::env::temp_dir().join(format!("api_gen_cpin_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("tmp dir");
        let emit = |asserts: Option<&crate::layout::TypeRegistry>| {
            Cgen::generate_header(
                dir.to_str().expect("utf8 path"),
                &defs[0],
                &BTreeMap::new(),
                &crate::naming::FL,
                Some("flowi"),
                false,
                asserts,
                "scripts/gen.sh",
            )
            .expect("header");
            std::fs::read_to_string(dir.join("pin").join("pin.h")).expect("read pin.h")
        };

        let off = emit(None);
        assert!(!off.contains("static_assert"), "pins stay opt-in: {off}");

        let on = emit(Some(&registry));
        let _ = std::fs::remove_dir_all(&dir);
        for expected in [
            "#include <assert.h>",
            "static_assert(sizeof(FlEntry) == 16, \"FlEntry size drift\");",
            "static_assert(offsetof(FlEntry, flag) == 0, \"FlEntry.flag offset drift\");",
            "static_assert(offsetof(FlEntry, count) == 4, \"FlEntry.count offset drift\");",
            "static_assert(offsetof(FlEntry, total) == 8, \"FlEntry.total offset drift\");",
        ] {
            assert!(on.contains(expected), "missing {expected}: {on}");
        }

        let Some(cc) = find_cc() else {
            eprintln!("C layout-pin compile test skipped: no cc on PATH");
            return;
        };
        assert!(
            compile_tu(cc, "c_pin_good", &on),
            "the pinned header compiles: {on}"
        );
        let bad = on.replace("sizeof(FlEntry) == 16", "sizeof(FlEntry) == 24");
        assert!(
            !compile_tu(cc, "c_pin_bad", &bad),
            "a wrong pin must fail to compile"
        );
    }

    /// A struct with an anonymous union is skipped by the pin pass: offsetof
    /// cannot name an unnamed member, so walking its fields would emit uncompilable
    /// C. Its union-free siblings in the same def still get pinned.
    #[test]
    fn c_layout_asserts_skip_anonymous_union_structs_but_not_their_siblings() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[module(pin)]\n\
             struct Tagged { kind: u32, union { count: u32, ratio: f32 } }\n\
             struct Plain { a: u32, b: u32 }",
            "pin.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let defs = vec![api_def];
        let registry = crate::layout::TypeRegistry::build(&defs);

        let dir = std::env::temp_dir().join(format!("api_gen_cpin_union_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("tmp dir");
        Cgen::generate_header(
            dir.to_str().expect("utf8 path"),
            &defs[0],
            &BTreeMap::new(),
            &crate::naming::FL,
            Some("flowi"),
            false,
            Some(&registry),
            "scripts/gen.sh",
        )
        .expect("header");
        let header = std::fs::read_to_string(dir.join("pin").join("pin.h")).expect("read pin.h");
        let _ = std::fs::remove_dir_all(&dir);

        assert!(
            !header.contains("FlTagged size drift") && !header.contains("offsetof(FlTagged"),
            "the union-bearing struct is not pinned: {header}"
        );
        assert!(
            header.contains("static_assert(sizeof(FlPlain) == 8, \"FlPlain size drift\");"),
            "its union-free sibling still is: {header}"
        );

        let Some(cc) = find_cc() else {
            eprintln!("union-skip compile test skipped: no cc on PATH");
            return;
        };
        assert!(
            compile_tu(cc, "c_pin_union", &header),
            "the header compiles: {header}"
        );
    }
}
