//! Inbound reading, emitted from the paired model: one file per def carrying a
//! host-side reader per record a slot takes as a parameter.
//!
//! What crosses this way is the plugin's, so none of it is trusted. A reader
//! takes the raw record by pointer and never forms a reference to it, and every
//! enum field decodes through its declared fallback - a stale or hostile
//! discriminant is a wrong answer, never undefined behavior.

use crate::api_parser::ApiDef;
use crate::emit_util::{
    group_imports, header, read_fn, type_name, write_doc, write_signature, write_use_list, Value,
};
use crate::pairing::{
    nested_enum, nested_record, nesting_order, slot_types, PairedEnum, PairedField, PairedModel,
    PairedStruct,
};
use heck::{ToShoutySnakeCase, ToSnakeCase};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufWriter, Write};

/// Where the emitted files reach for the types and helpers they use.
pub struct InboundPaths<'a> {
    /// Crate holding the raw ABI modules: `<crate>::<def>` is aliased to abi.
    pub abi_crate: &'a str,
    /// Verbatim use paths the emitted code needs - the slice-borrowing helper.
    pub uses: &'a [String],
    /// Regeneration script named in the emitted header.
    pub script: &'a str,
}

/// Every record a slot takes as a parameter, each after what it nests. A `[with]`
/// field is the helper's, so what it nests is never reached.
pub fn inbound(api_defs: &[&ApiDef], model: &PairedModel) -> Vec<String> {
    let roots = slot_types(api_defs, model, false);
    nesting_order(model, roots.iter().map(String::as_str), |f| {
        f.with.is_none()
    })
}

/// Emit one module per def with inbound records, answering their module names.
pub fn generate(
    dir: &str,
    inbound: &[String],
    model: &PairedModel,
    paths: &InboundPaths,
) -> std::io::Result<Vec<String>> {
    let mut per_def: BTreeMap<&str, Vec<&PairedStruct>> = BTreeMap::new();
    for name in inbound {
        let paired = &model.structs[name];
        per_def.entry(&paired.def).or_default().push(paired);
    }

    // Before any file is opened: a refusal partway through emission would leave a
    // truncated module on disk for the next build to trip over.
    for structs in per_def.values() {
        for paired in structs {
            assert!(
                !paired.found_synthesis,
                "api_gen: `{}` crosses inbound but synthesizes `found`, which only the publish \
                 side means: drop the field or give the slot a hand-written read",
                paired.name
            );
            for field in own_fields(paired) {
                if let Some(paired_enum) = nested_enum(model, field) {
                    fallback(paired_enum);
                }
            }
        }
    }

    let mut modules = Vec::new();
    for (def, structs) in &per_def {
        let module = format!("{}_inbound", def);
        write_module(dir, &module, def, structs, model, paths)?;
        modules.push(module);
    }
    Ok(modules)
}

/// The variant an undeclared value decodes to, which the read emitter cannot
/// proceed without: it has nowhere else to land.
pub fn fallback(paired: &PairedEnum) -> &str {
    paired.fallback.as_deref().unwrap_or_else(|| {
        panic!(
            "api_gen: `{}` is read inbound but declares no fallback: give it \
             `#[view(<path>, fallback = <variant>)]`, so a value the def never declared decodes \
             to a wrong answer rather than to undefined behavior",
            paired.name
        )
    })
}

fn write_module(
    dir: &str,
    module: &str,
    def: &str,
    structs: &[&PairedStruct],
    model: &PairedModel,
    paths: &InboundPaths,
) -> std::io::Result<()> {
    let mut f = BufWriter::new(File::create(format!("{}/{}.rs", dir, module))?);

    writeln!(f, "{}", header(paths.script))?;
    writeln!(f, "//! Reads {}.def's inbound records off the ABI.", def)?;
    writeln!(f, "//!")?;
    writeln!(
        f,
        "//! SAFETY: every reader requires what raw addresses to stay valid and unmodified"
    )?;
    writeln!(
        f,
        "//! for the call - its stated contract - and every unsafe block reads through it."
    )?;
    writeln!(f, "#![allow(clippy::undocumented_unsafe_blocks)]")?;
    writeln!(f, "#![allow(unsafe_code)]")?;
    writeln!(f)?;
    writeln!(f, "use core::ptr;")?;
    if structs.iter().any(|paired| has_scalar_list(model, paired)) {
        for path in paths.uses {
            writeln!(f, "use {};", path)?;
        }
    }
    writeln!(f)?;
    writeln!(f, "use {}::{} as abi;", paths.abi_crate, def)?;
    writeln!(f)?;

    let enums = decoded_enums(model, structs);
    let views = structs
        .iter()
        .map(|paired| paired.view.as_str())
        .chain(enums.iter().map(|e| e.view.as_str()));
    for (module, types) in group_imports(views) {
        write_use_list(&mut f, module, &types)?;
    }

    for paired_enum in &enums {
        write_decode(&mut f, paired_enum, def)?;
    }
    for paired in structs {
        write_read(&mut f, paired, model)?;
    }
    Ok(())
}

/// The enums the readers in one module decode, by name. A `[with]` field's enum
/// is the helper's, so it is not one of them.
fn decoded_enums<'a>(model: &'a PairedModel, structs: &[&'a PairedStruct]) -> Vec<&'a PairedEnum> {
    let mut enums: BTreeMap<&str, &PairedEnum> = BTreeMap::new();
    for paired in structs {
        for field in own_fields(paired) {
            if let Some(paired_enum) = nested_enum(model, field) {
                enums.insert(&paired_enum.name, paired_enum);
            }
        }
    }
    enums.into_values().collect()
}

/// `pub(crate) fn <enum>_from_raw(raw: <int>) -> <HostEnum>` - every declared
/// discriminant named through the ABI type, everything else the fallback.
fn write_decode(f: &mut impl Write, paired: &PairedEnum, def: &str) -> std::io::Result<()> {
    let host = type_name(&paired.view);
    let fallback = fallback(paired);

    writeln!(f)?;
    write_doc(
        f,
        &format!(
            "Decode an inbound `abi::{}`. A value `{}.def` does not declare reads as `{}`.",
            paired.name, def, fallback
        ),
    )?;
    writeln!(
        f,
        "pub(crate) fn {}(raw: {}) -> {} {{",
        decode_fn(&paired.name),
        int_type(paired),
        host
    )?;
    for variant in &paired.variants {
        writeln!(
            f,
            "    const {}: {} = abi::{}::{} as {};",
            variant.name.to_shouty_snake_case(),
            int_type(paired),
            paired.name,
            variant.name,
            int_type(paired)
        )?;
    }
    writeln!(f, "    match raw {{")?;
    for variant in &paired.variants {
        writeln!(
            f,
            "        {} => {}::{},",
            variant.name.to_shouty_snake_case(),
            host,
            variant.host
        )?;
    }
    writeln!(f, "        _ => {}::{},", host, fallback)?;
    writeln!(f, "    }}")?;
    writeln!(f, "}}")
}

/// The integer an enum crosses as, which is what a reader decodes from: a packed
/// enum is one byte wide, everything else the C default.
pub fn int_type(paired: &PairedEnum) -> &'static str {
    if paired.packed {
        "u8"
    } else {
        "u32"
    }
}

fn write_read(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
) -> std::io::Result<()> {
    let view = type_name(&paired.view);

    writeln!(f)?;
    write_doc(
        f,
        &format!(
            "Read an inbound `abi::{}` into a [`{}`].",
            paired.name, view
        ),
    )?;
    writeln!(f, "///")?;
    writeln!(f, "/// # Safety")?;
    write_doc(
        f,
        &format!(
            "`raw` must address one initialised `abi::{}` for the call, whose pointer fields \
             address their stated counts.",
            paired.name
        ),
    )?;
    write_signature(
        f,
        &format!("pub(crate) unsafe fn {}(", read_fn(&paired.name)),
        &[format!("raw: *const abi::{}", paired.name)],
        &format!(") -> {} {{", view),
    )?;
    writeln!(f, "    unsafe {{")?;

    for field in paired.fields.iter().filter(is_own_list) {
        write_list_binding(f, field, model)?;
    }

    writeln!(f, "        {} {{", view)?;
    for field in &paired.fields {
        // A list is already bound, under the name the record literal wants.
        if is_own_list(&field) {
            writeln!(f, "            {},", field.host)?;
            continue;
        }
        field_value(model, field).write(f, "            ", &format!("{}:", field.host), ",")?;
    }
    writeln!(f, "        }}")?;
    writeln!(f, "    }}")?;
    writeln!(f, "}}")
}

/// The let a list field is copied out through, ahead of the record literal.
fn write_list_binding(
    f: &mut impl Write,
    field: &PairedField,
    model: &PairedModel,
) -> std::io::Result<()> {
    let count = field.count.as_ref().expect("a list field is fused");
    let Some(ty) = nested_record(model, field) else {
        let borrow = Value::Call {
            head: "borrow_slice".to_owned(),
            args: vec![read_at(&field.name), format!("{} as usize", read_at(count))],
            tail: ".to_vec()".to_owned(),
        };
        return borrow.write(f, "        ", &format!("let {} =", field.host), ";");
    };

    // A record's elements are walked through the base pointer rather than through
    // a slice: forming one would materialise every discriminant they carry.
    writeln!(f, "        let base = {};", read_at(&field.name))?;
    writeln!(
        f,
        "        let count = if base.is_null() {{ 0 }} else {{ {} as usize }};",
        read_at(count)
    )?;
    let mapped = format!("(0..count).map(|i| {}(base.add(i))).collect()", read_fn(ty));
    Value::Plain(mapped).write(f, "        ", &format!("let {} =", field.host), ";")
}

/// What one field reads as, as an expression over raw.
fn field_value(model: &PairedModel, field: &PairedField) -> Value {
    if let Some(helper) = &field.with {
        let args = match &field.count {
            Some(count) => vec![read_at(&field.name), read_at(count)],
            None => vec![scalar_read(model, field)],
        };
        return Value::Call {
            head: helper.clone(),
            args,
            tail: String::new(),
        };
    }

    if field.ty == "String" {
        return Value::Call {
            head: "ptr::read".to_owned(),
            args: vec![format!("ptr::addr_of!((*raw).{})", field.name)],
            tail: ".into_string()".to_owned(),
        };
    }
    if let Some(ty) = nested_record(model, field) {
        return Value::Call {
            head: read_fn(ty),
            args: vec![format!("ptr::addr_of!((*raw).{})", field.name)],
            tail: String::new(),
        };
    }
    if let Some(paired) = nested_enum(model, field) {
        return Value::Call {
            head: decode_fn(&paired.name),
            args: vec![read_as(&field.name, int_type(paired))],
            tail: String::new(),
        };
    }
    Value::Plain(scalar_read(model, field))
}

/// One non-list field read out of raw. An enum and a bool are read as the
/// integer they cross as: not every byte is one of their values.
fn scalar_read(model: &PairedModel, field: &PairedField) -> String {
    if let Some(paired) = nested_enum(model, field) {
        return read_as(&field.name, int_type(paired));
    }
    if field.ty == "bool" {
        return format!("{} != 0", read_as(&field.name, "u8"));
    }
    read_at(&field.name)
}

/// A field read out of raw as the type it is declared with.
fn read_at(name: &str) -> String {
    format!("ptr::read(ptr::addr_of!((*raw).{}))", name)
}

fn read_as(name: &str, ty: &str) -> String {
    format!("ptr::read(ptr::addr_of!((*raw).{}).cast::<{}>())", name, ty)
}

/// The fields the generated inbound side handles itself; a `[with]` field is the
/// helper's.
pub fn own_fields(paired: &PairedStruct) -> impl Iterator<Item = &PairedField> {
    paired.fields.iter().filter(|field| field.with.is_none())
}

fn is_own_list(field: &&PairedField) -> bool {
    field.with.is_none() && field.count.is_some()
}

/// Whether paired copies a scalar list out, which is the only thing a reader
/// borrows a slice for.
fn has_scalar_list(model: &PairedModel, paired: &PairedStruct) -> bool {
    paired
        .fields
        .iter()
        .filter(is_own_list)
        .any(|field| nested_record(model, field).is_none())
}

fn decode_fn(name: &str) -> String {
    format!("{}_from_raw", name.to_snake_case())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::ApiParser;

    /// Every shape a reader lowers: a string, a scalar list, a nested record, an
    /// enum with its fallback and a variant rename, and the `[with]` hatch over a
    /// fused list.
    const DEMOZOO: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        extern opaque FlArena\n\
        #[view(crate::demoscene::query::SortOrder, fallback = Relevance)]\n\
        enum DemozooSort {\n\
            Relevance = 0,\n\
            [from(TitleAz)] NameAsc = 1,\n\
        }\n\
        struct DemozooExprNode { op: u32, value: u32, text: String }\n\
        struct DemozooFilter {\n\
            country: String,\n\
            platforms_any: *const u32,\n\
            platforms_any_count: u32,\n\
            [from(tree)] [with(crate::demozoo_abi::read_tree)] expr: *const DemozooExprNode,\n\
            expr_count: u32,\n\
        }\n\
        struct DemozooQuery {\n\
            text: String,\n\
            [from(entities)] [with(crate::seams::entities)] entity_mask: u32,\n\
            sort: DemozooSort,\n\
            limit: u32,\n\
            randomize: bool,\n\
            filter: DemozooFilter,\n\
        }\n\
        struct DemozooProduction { title: String, found: bool }\n\
        #[attributes(service)]\n\
        api Demozoo {\n\
            rp_demozoo_get_production(id: u32, arena: *FlArena) -> DemozooProduction\n\
            rp_demozoo_slot_update(slot: u32, query: *const DemozooQuery) -> u32\n\
        }";

    /// A record list crossing inbound un-hatched, and a packed enum: the two
    /// shapes no demozoo slot carries.
    const CATALOG: &str = "\
        #[module(catalog)]\n\
        #[views(crate::catalog::data)]\n\
        #[attributes(packed)]\n\
        #[view(crate::catalog::Kind, fallback = Unknown)]\n\
        enum CatalogKind {\n\
            Item = 0,\n\
            [from(Set)] Group = 1,\n\
        }\n\
        struct CatalogTerm { id: u32, kind: CatalogKind }\n\
        struct CatalogQuery {\n\
            terms: *const CatalogTerm,\n\
            term_count: u32,\n\
        }\n\
        api Catalog { rp_catalog_slot_update(slot: u32, query: *const CatalogQuery) -> u32 }";

    fn parse(src: &str) -> Vec<ApiDef> {
        let module = src.split("#[module(").nth(1).expect("a module directive");
        let module = module.split(')').next().expect("a closed directive");
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(src, &format!("{}.def", module), &mut api_def);
        vec![api_def]
    }

    /// Emit src's inbound modules into a temp dir and answer the one file.
    fn emit(src: &str, case: &str) -> String {
        let api_defs = parse(src);
        let model = crate::pairing::resolve(&api_defs).expect("pairs");
        let dir =
            std::env::temp_dir().join(format!("api_gen_inbound_{}_{}", std::process::id(), case));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let modules = generate(
            dir.to_str().expect("utf8"),
            &inbound(&crate::pairing::as_refs(&api_defs), &model),
            &model,
            &InboundPaths {
                abi_crate: "replay_plugin",
                uses: &["flowi::boundary::borrow_slice".to_owned()],
                script: "scripts/gen.sh",
            },
        )
        .expect("emit");
        let module = modules.first().expect("one module").clone();
        std::fs::read_to_string(dir.join(format!("{}.rs", module))).expect("read")
    }

    /// Only what a slot takes as a parameter, and only what that reaches through
    /// a field the reader lowers itself: DemozooExprNode is the `[with]`
    /// helper's, and DemozooProduction is only ever returned.
    #[test]
    fn only_parameter_position_records_are_read() {
        let api_defs = parse(DEMOZOO);
        let model = crate::pairing::resolve(&api_defs).expect("pairs");

        assert_eq!(
            inbound(&crate::pairing::as_refs(&api_defs), &model),
            ["DemozooFilter", "DemozooQuery"]
        );
    }

    #[test]
    fn a_reader_takes_the_record_by_pointer() {
        let emitted = emit(DEMOZOO, "pointer");

        assert!(
            emitted.contains(
                "pub(crate) unsafe fn read_demozoo_query(raw: *const abi::DemozooQuery) \
                 -> QueryView {"
            ),
            "{}",
            emitted
        );
        assert!(emitted.contains("text: ptr::read(ptr::addr_of!((*raw).text)).into_string(),"));
        assert!(emitted.contains("limit: ptr::read(ptr::addr_of!((*raw).limit)),"));
        // A bool is validity-constrained like an enum: not every byte is one.
        assert!(
            emitted.contains(
                "randomize: ptr::read(ptr::addr_of!((*raw).randomize).cast::<u8>()) != 0,"
            ),
            "{}",
            emitted
        );
    }

    /// A record list is walked through its base pointer - a slice of the elements
    /// would materialise every discriminant they carry. A null base reads as no
    /// elements whatever the count says.
    #[test]
    fn a_record_list_is_walked_through_its_base_pointer() {
        let emitted = emit(CATALOG, "record_list");

        assert!(
            emitted.contains(
                "        let base = ptr::read(ptr::addr_of!((*raw).terms));\n\
                 \x20       let count = if base.is_null() { 0 } else { \
                 ptr::read(ptr::addr_of!((*raw).term_count)) as usize };\n\
                 \x20       let terms = (0..count).map(|i| read_catalog_term(base.add(i))).collect();\n"
            ),
            "{}",
            emitted
        );
        assert!(!emitted.contains("borrow_slice"), "{}", emitted);
    }

    #[test]
    fn a_packed_enum_decodes_from_one_byte() {
        let emitted = emit(CATALOG, "packed");

        assert!(emitted.contains("pub(crate) fn catalog_kind_from_raw(raw: u8) -> Kind {"));
        assert!(emitted.contains("const GROUP: u8 = abi::CatalogKind::Group as u8;"));
        assert!(emitted.contains("GROUP => Kind::Set,"));
        assert!(
            emitted.contains(
                "kind: catalog_kind_from_raw(ptr::read(ptr::addr_of!((*raw).kind).cast::<u8>())),"
            ),
            "{}",
            emitted
        );
    }

    /// found is a publish-side synthesis: inbound there is no Option for it to
    /// answer, and the refusal fires before any file is opened.
    #[test]
    #[should_panic(expected = "`DemozooQuery` crosses inbound but synthesizes `found`")]
    fn an_inbound_record_synthesizing_found_is_refused() {
        let src = DEMOZOO.replace("text: String,", "found: bool,");
        emit(&src, "found");
    }

    #[test]
    fn an_enum_decodes_through_its_fallback() {
        let emitted = emit(DEMOZOO, "fallback");

        assert!(emitted.contains("pub(crate) fn demozoo_sort_from_raw(raw: u32) -> SortOrder {"));
        assert!(emitted.contains("const NAME_ASC: u32 = abi::DemozooSort::NameAsc as u32;"));
        assert!(emitted.contains("NAME_ASC => SortOrder::TitleAz,"));
        assert!(emitted.contains("_ => SortOrder::Relevance,"));
        assert!(
            emitted.contains(
                "sort: demozoo_sort_from_raw(ptr::read(ptr::addr_of!((*raw).sort).cast::<u32>())),"
            ),
            "{}",
            emitted
        );
    }

    #[test]
    fn a_with_hatch_takes_the_field_whole() {
        let emitted = emit(DEMOZOO, "with");

        assert!(
            emitted.contains(
                "tree: crate::demozoo_abi::read_tree(\n\
                 \x20               ptr::read(ptr::addr_of!((*raw).expr)),\n\
                 \x20               ptr::read(ptr::addr_of!((*raw).expr_count)),\n\
                 \x20           ),"
            ),
            "{}",
            emitted
        );
        assert!(emitted.contains("entities: crate::seams::entities(ptr::read("));
        // The neighbours of a hatched field are still generated.
        assert!(
            emitted.contains("country: ptr::read(ptr::addr_of!((*raw).country)).into_string(),")
        );
    }

    #[test]
    fn a_scalar_list_is_copied_out() {
        let emitted = emit(DEMOZOO, "list");

        assert!(emitted.contains("use flowi::boundary::borrow_slice;"));
        assert!(
            emitted.contains(
                "let platforms_any = borrow_slice(\n\
                 \x20           ptr::read(ptr::addr_of!((*raw).platforms_any)),\n\
                 \x20           ptr::read(ptr::addr_of!((*raw).platforms_any_count)) as usize,\n\
                 \x20       )\n\
                 \x20       .to_vec();\n"
            ),
            "{}",
            emitted
        );
    }

    #[test]
    #[should_panic(expected = "`DemozooSort` is read inbound but declares no fallback")]
    fn an_enum_read_inbound_without_a_fallback_is_refused() {
        let src = DEMOZOO.replace(", fallback = Relevance", "");
        emit(&src, "no_fallback");
    }
}
