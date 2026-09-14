//! Consume-side reading, emitted from the paired model: one file per def carrying
//! a reader per `#[read]` record and everything it nests. A reader takes the raw
//! record and answers the owned type.

use crate::emit_util::{
    group_imports, header, read_fn, type_name, write_doc, write_signature, write_use_list, Value,
    WIDTH,
};
use crate::pairing::{nested_record, nesting_order, PairedField, PairedModel, PairedStruct};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{BufWriter, Write};

/// Where the emitted files reach for the types and helpers they use.
pub struct ReadPaths<'a> {
    /// Module holding the raw ABI modules: `<path>::<def>` is aliased to abi.
    pub abi_path: &'a str,
    /// Verbatim use paths the emitted code needs - the slice-borrowing helper.
    pub uses: &'a [String],
    /// Regeneration script named in the emitted header.
    pub script: &'a str,
}

/// Emit one module per def with readers, answering their module names.
pub fn generate(dir: &str, model: &PairedModel, paths: &ReadPaths) -> std::io::Result<Vec<String>> {
    let mut per_def: BTreeMap<&str, Vec<&PairedStruct>> = BTreeMap::new();
    for name in emission_order(model) {
        let paired = &model.structs[&name];
        per_def.entry(&paired.def).or_default().push(paired);
    }

    // Before any file is opened: a refusal partway through emission would leave a
    // truncated module on disk.
    for structs in per_def.values() {
        for paired in structs {
            owned_path(paired);
            reject_nested_option(model, paired);
        }
    }

    let mut modules = Vec::new();
    for (def, structs) in &per_def {
        let module = format!("{}_read", def);
        write_module(dir, &module, def, structs, model, paths)?;
        modules.push(module);
    }
    Ok(modules)
}

/// An optional record answers Option. A field holds one; a Vec element cannot.
fn reject_nested_option(model: &PairedModel, paired: &PairedStruct) {
    for field in own_fields(model, &paired.name).filter(|f| f.count.is_some()) {
        if let Some(ty) = nested_record(model, field) {
            assert!(
                !model.structs[ty].found_synthesis,
                "api_gen: `{}.{}` lists the optional record `{}`, which reads as an `Option`: \
                 give the field `[read_with(<helper path>)]`",
                paired.name, field.name, ty
            );
        }
    }
}

/// Every `#[read]` record and everything it nests, each after what it nests. A
/// `[read_with]` field is the helper's, so what it nests is never reached.
fn emission_order(model: &PairedModel) -> Vec<String> {
    let roots = model
        .structs
        .values()
        .filter(|s| s.read_root)
        .map(|s| s.name.as_str());
    nesting_order(model, roots, |field| field.read_with.is_none())
}

fn write_module(
    dir: &str,
    module: &str,
    def: &str,
    structs: &[&PairedStruct],
    model: &PairedModel,
    paths: &ReadPaths,
) -> std::io::Result<()> {
    let mut f = BufWriter::new(File::create(format!("{}/{}.rs", dir, module))?);

    writeln!(f, "{}", header(paths.script))?;
    writeln!(f, "//! Reads {}.def's paired records off the ABI.", def)?;
    if structs
        .iter()
        .any(|paired| reads_unsafely(model, &paired.name))
    {
        writeln!(f, "//!")?;
        writeln!(
            f,
            "//! SAFETY: every reader requires what the raw record addresses to stay valid for"
        )?;
        writeln!(
            f,
            "//! as long as it answers for - its stated contract - and every unsafe block"
        )?;
        writeln!(
            f,
            "//! borrows from it. The record itself is only read during the call."
        )?;
        writeln!(f, "#![allow(clippy::undocumented_unsafe_blocks)]")?;
        writeln!(f, "#![allow(unsafe_code)]")?;
    }
    writeln!(f)?;
    if structs.iter().any(has_list) {
        for path in paths.uses {
            writeln!(f, "use {};", path)?;
        }
        writeln!(f)?;
    }
    writeln!(f, "use {}::{} as abi;", paths.abi_path, def)?;
    writeln!(f)?;
    for (module, types) in group_imports(structs.iter().map(|s| owned_path(s))) {
        write_use_list(&mut f, module, &types)?;
    }

    for paired in structs {
        write_read(&mut f, paired, model)?;
    }
    Ok(())
}

fn write_read(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
) -> std::io::Result<()> {
    let ty = owned_type(paired);
    let lifetime = if borrows(model, &paired.name) {
        "<'a>"
    } else {
        ""
    };
    let unsafety = if reads_unsafely(model, &paired.name) {
        "unsafe "
    } else {
        ""
    };
    let answer = if paired.found_synthesis {
        format!("Option<{}{}>", ty, lifetime)
    } else {
        format!("{}{}", ty, lifetime)
    };

    writeln!(f)?;
    if !unsafety.is_empty() {
        writeln!(f, "/// # Safety")?;
        // Nothing is held past the call when there is no 'a to hold it for.
        write_doc(
            f,
            if lifetime.is_empty() {
                "Everything `raw` addresses must stay valid and unmodified for the duration of \
                 the call."
            } else {
                "Everything `raw` addresses must stay valid and unmodified for the whole of \
                 `'a`. `raw` itself is only read during the call."
            },
        )?;
    }

    write_signature(
        f,
        &format!("pub {}fn {}{}(", unsafety, read_fn(&paired.name), lifetime),
        &[format!("raw: &abi::{}", paired.name)],
        &format!(") -> {} {{", answer),
    )?;

    if paired.found_synthesis {
        writeln!(f, "    if !raw.found {{")?;
        writeln!(f, "        return None;")?;
        writeln!(f, "    }}")?;
    }

    // A list is bound first: the collect reads as a statement, not as an arm of
    // the record literal below.
    for field in paired.fields.iter().filter(|f| f.count.is_some()) {
        let count = field.count.as_ref().expect("a list field is fused");
        let borrow = format!(
            "unsafe {{ borrow_slice(raw.{}, raw.{} as usize) }}",
            field.name, count
        );
        match &field.nested {
            Some(ty) => {
                write_let(f, &format!("raw_{}", field.name), &borrow)?;
                let read = element_read(model, ty);
                let mapped = format!("raw_{}.iter().map({}).collect()", field.name, read);
                if fits_let(&field.name, &mapped) {
                    write_let(f, &field.name, &mapped)?;
                } else {
                    writeln!(f, "    let {} = raw_{}", field.name, field.name)?;
                    writeln!(f, "        .iter()")?;
                    writeln!(f, "        .map({})", read)?;
                    writeln!(f, "        .collect();")?;
                }
            }
            None => write_let(f, &field.name, &borrow)?,
        }
    }

    let (open, close) = if paired.found_synthesis {
        (format!("    Some({} {{", ty), "    })")
    } else {
        (format!("    {} {{", ty), "    }")
    };
    let indent = "        ";
    writeln!(f, "{}", open)?;
    for field in &paired.fields {
        if let Some(helper) = &field.read_with {
            writeln!(
                f,
                "{}{}: {}(raw.{}),",
                indent, field.name, helper, field.name
            )?;
        } else if field.count.is_some() {
            writeln!(f, "{}{},", indent, field.name)?;
        } else if field.ty == "String" {
            writeln!(
                f,
                "{}{}: unsafe {{ raw.{}.as_str() }},",
                indent, field.name, field.name
            )?;
        } else if let Some(nested) = nested_record(model, field) {
            let call = format!("{}(&raw.{})", read_fn(nested), field.name);
            let call = if reads_unsafely(model, nested) {
                format!("unsafe {{ {} }}", call)
            } else {
                call
            };
            writeln!(f, "{}{}: {},", indent, field.name, call)?;
        } else {
            writeln!(f, "{}{}: raw.{},", indent, field.name, field.name)?;
        }
    }
    writeln!(f, "{}", close)?;
    writeln!(f, "}}")
}

fn fits_let(name: &str, expr: &str) -> bool {
    "    let  = ;".len() + name.len() + expr.len() <= WIDTH
}

/// `let <name> = <expr>;`, wrapping the expression onto its own line when the
/// one-liner runs over.
fn write_let(f: &mut impl Write, name: &str, expr: &str) -> std::io::Result<()> {
    Value::Plain(expr.to_owned()).write(f, "    ", &format!("let {} =", name), ";")
}

/// How a list element is read: an unsafe reader needs the block, a safe one is
/// a plain function reference.
fn element_read(model: &PairedModel, ty: &str) -> String {
    if reads_unsafely(model, ty) {
        format!("|item| unsafe {{ {}(item) }}", read_fn(ty))
    } else {
        read_fn(ty)
    }
}

/// The fields a reader lowers itself; a `[read_with]` field is the helper's.
fn own_fields<'a>(model: &'a PairedModel, name: &str) -> impl Iterator<Item = &'a PairedField> {
    model.structs[name]
        .fields
        .iter()
        .filter(|field| field.read_with.is_none())
}

/// Whether name has a list field, which is the only thing a reader borrows
/// a slice for.
fn has_list(paired: &&PairedStruct) -> bool {
    paired
        .fields
        .iter()
        .any(|field| field.read_with.is_none() && field.count.is_some())
}

/// Whether name or anything it nests has a field satisfying leaf. A record
/// can reach itself through a pointer list, so re-entry answers false - the
/// least fixpoint, and what both callers below want.
fn any_nested_field(model: &PairedModel, name: &str, leaf: &impl Fn(&PairedField) -> bool) -> bool {
    fn walk(
        model: &PairedModel,
        name: &str,
        leaf: &impl Fn(&PairedField) -> bool,
        seen: &mut BTreeSet<String>,
    ) -> bool {
        if !seen.insert(name.to_owned()) {
            return false;
        }
        own_fields(model, name).any(|field| {
            leaf(field) || nested_record(model, field).is_some_and(|ty| walk(model, ty, leaf, seen))
        })
    }

    walk(model, name, leaf, &mut BTreeSet::new())
}

/// Whether the owned type holds a borrow of what the raw record addresses - a
/// string, a scalar list, or a nested type that does. That is what carries the
/// 'a. A record list does not: its elements are read into an owned Vec.
pub fn borrows(model: &PairedModel, name: &str) -> bool {
    any_nested_field(model, name, &|field| {
        field.ty == "String" || (field.count.is_some() && field.nested.is_none())
    })
}

/// Whether reading name takes an unsafe operation - a string, any list, or a
/// nested type that does.
pub fn reads_unsafely(model: &PairedModel, name: &str) -> bool {
    any_nested_field(model, name, &|field| {
        field.ty == "String" || field.count.is_some()
    })
}

/// The consume-side type's path. Also where a `#[read]` record with no
/// consume-side name is refused: pairing pairs leniently.
fn owned_path(paired: &PairedStruct) -> &str {
    paired.owned.as_deref().unwrap_or_else(|| {
        panic!(
            "api_gen: `{}` is read but `{}.def` declares no `#[reads(<plugin module path>)]`",
            paired.name, paired.def
        )
    })
}

fn owned_type(paired: &PairedStruct) -> &str {
    type_name(owned_path(paired))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::ApiParser;

    const DEMOZOO: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        #[reads(crate::services::demozoo)]\n\
        extern opaque FlArena\n\
        struct DemozooPlacingEntry { production_id: u32, position: u16 }\n\
        struct DemozooCompetition {\n\
            name: String,\n\
            placings: *const DemozooPlacingEntry,\n\
            placing_count: u32,\n\
        }\n\
        #[read]\n\
        struct DemozooPartyDetail {\n\
            name: String,\n\
            [read_with(crate::services::demozoo::entity_id)] series_id: u32,\n\
            competitions: *const DemozooCompetition,\n\
            competition_count: u32,\n\
            soundtracks: *const u32,\n\
            soundtrack_count: u32,\n\
            found: bool,\n\
        }\n\
        #[read]\n\
        struct DemozooHeat { entries: *const DemozooPlacingEntry, count: u32 }\n\
        #[read(Held)]\n\
        struct DemozooResult { ids: *const u32, count: u32 }\n\
        #[read]\n\
        struct DemozooBadge { id: u32, found: bool }\n\
        enum DemozooSupertype { Any, Production }\n\
        #[read]\n\
        struct DemozooParty {\n\
            name: String,\n\
            supertype: DemozooSupertype,\n\
            found: bool,\n\
        }\n\
        api Demozoo {\n\
            rp_demozoo_get_party(id: u32, arena: *FlArena) -> DemozooParty\n\
            rp_demozoo_get_party_detail(id: u32, arena: *FlArena) -> DemozooPartyDetail\n\
            rp_demozoo_get_heat(id: u32, arena: *FlArena) -> DemozooHeat\n\
            rp_demozoo_get_result(id: u32, arena: *FlArena) -> DemozooResult\n\
            rp_demozoo_get_badge(id: u32) -> DemozooBadge\n\
        }";

    fn emit(tag: &str) -> String {
        emit_src(tag, DEMOZOO)
    }

    fn emit_src(tag: &str, src: &str) -> String {
        let dir = std::env::temp_dir().join(format!("api_gen_read_{}_{}", std::process::id(), tag));
        std::fs::create_dir_all(&dir).expect("create temp dir");

        let mut api_def = crate::api_parser::ApiDef::default();
        ApiParser::parse_string(src, "demozoo.def", &mut api_def);
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);
        let model = crate::pairing::resolve(&api_defs).expect("pairs");

        let modules = generate(
            dir.to_str().unwrap(),
            &model,
            &ReadPaths {
                abi_path: "crate::generated",
                uses: &["flowi::boundary::borrow_slice".to_owned()],
                script: "scripts/gen.sh",
            },
        )
        .expect("generate");
        assert_eq!(modules, ["demozoo_read"]);

        let emitted = std::fs::read_to_string(dir.join("demozoo_read.rs")).expect("read emitted");
        let _ = std::fs::remove_dir_all(&dir);
        emitted
    }

    #[test]
    fn an_enum_field_is_copied_rather_than_read() {
        let emitted = emit("enum_field");

        assert!(emitted.contains("        supertype: raw.supertype,"));
        assert!(!emitted.contains("read_demozoo_supertype"));
    }

    #[test]
    fn a_nested_record_is_read_before_the_record_that_nests_it() {
        let emitted = emit("nesting");

        let entry = emitted
            .find("fn read_demozoo_placing_entry")
            .expect("entry");
        let competition = emitted
            .find("fn read_demozoo_competition")
            .expect("competition");
        let detail = emitted
            .find("fn read_demozoo_party_detail")
            .expect("detail");
        assert!(entry < competition && competition < detail);
    }

    #[test]
    fn an_optional_record_answers_an_option() {
        let emitted = emit("optional");

        assert!(emitted.contains(
            "pub unsafe fn read_demozoo_party_detail<'a>(\n\
             \x20   raw: &abi::DemozooPartyDetail,\n\
             ) -> Option<PartyDetail<'a>> {\n\
             \x20   if !raw.found {\n\
             \x20       return None;\n\
             \x20   }"
        ));
    }

    #[test]
    fn a_record_that_borrows_nothing_reads_safely() {
        let emitted = emit("scalar_only");

        assert!(emitted.contains(
            "pub fn read_demozoo_placing_entry(raw: &abi::DemozooPlacingEntry) -> PlacingEntry {"
        ));
        assert!(emitted.contains(
            "let placings = raw_placings.iter().map(read_demozoo_placing_entry).collect();"
        ));
    }

    #[test]
    fn list_elements_are_read_by_what_they_borrow() {
        let emitted = emit("lists");

        assert!(emitted.contains(".map(|item| unsafe { read_demozoo_competition(item) })"));
        assert!(emitted.contains(
            "    let soundtracks = unsafe { borrow_slice(raw.soundtracks, raw.soundtrack_count as usize) };"
        ));
    }

    #[test]
    fn a_read_with_field_and_an_unreached_record() {
        let emitted = emit("hatch");

        assert!(emitted.contains("series_id: crate::services::demozoo::entity_id(raw.series_id),"));
        assert!(!emitted.contains("read_demozoo_party("));
    }

    /// The lifetime and the unsafe are decided separately.
    #[test]
    fn a_list_of_scalar_only_records_takes_unsafe_without_a_lifetime() {
        assert!(emit("no_lifetime")
            .contains("pub unsafe fn read_demozoo_heat(raw: &abi::DemozooHeat) -> Heat {"));
    }

    /// The convention would derive Result from DemozooResult, shadowing the
    /// prelude.
    #[test]
    fn a_read_override_names_the_owned_type() {
        let emitted = emit("owned_name");

        assert!(emitted.contains("pub unsafe fn read_demozoo_result<'a>"));
        assert!(emitted.contains("-> Held<'a> {"));
        assert!(!emitted.contains("Result<'a>"));
    }

    /// Optional and borrowing are independent.
    #[test]
    fn an_optional_record_that_borrows_nothing_reads_safely() {
        assert!(emit("safe_option")
            .contains("pub fn read_demozoo_badge(raw: &abi::DemozooBadge) -> Option<Badge> {"));
    }

    #[test]
    fn a_record_reached_twice_is_emitted_once() {
        let emitted = emit("dedup");

        assert_eq!(emitted.matches("fn read_demozoo_placing_entry(").count(), 1);
    }

    /// The slice helper is imported only where a list is actually lowered - an
    /// unused import fails the consumer's -D warnings lane.
    #[test]
    fn a_def_with_no_list_imports_no_slice_helper() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            #[read]\n\
            struct DemozooBadge { id: u32 }\n\
            api Demozoo { rp_demozoo_get_badge(id: u32) -> DemozooBadge }";

        let emitted = emit_src("no_list", src);
        assert!(!emitted.contains("borrow_slice"));
        // Nothing warns about an unused `#![allow]`, so only a negative assert
        // catches a spurious exemption.
        assert!(!emitted.contains("unsafe_code"));
    }

    #[test]
    #[should_panic(expected = "declares no `#[reads(")]
    fn a_read_record_without_a_reads_directive_is_refused() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[read]\n\
            struct DemozooBadge { id: u32 }\n\
            api Demozoo { rp_demozoo_get_badge(id: u32) -> DemozooBadge }";

        emit_src("no_reads", src);
    }

    #[test]
    fn a_record_that_reaches_itself_through_a_list_terminates() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            #[read]\n\
            struct DemozooNode { id: u32, children: *const DemozooNode, count: u32 }\n\
            api Demozoo { rp_demozoo_get_node(id: u32) -> DemozooNode }";

        // No string anywhere in the cycle, so it carries no 'a; the list still
        // takes the unsafe borrow.
        assert!(emit_src("cycle", src)
            .contains("pub unsafe fn read_demozoo_node(raw: &abi::DemozooNode) -> Node {"));
    }

    #[test]
    #[should_panic(expected = "lists the optional record `DemozooBadge`")]
    fn a_list_of_an_optional_record_is_refused() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            struct DemozooBadge { id: u32, found: bool }\n\
            #[read]\n\
            struct DemozooHeat { badges: *const DemozooBadge, count: u32 }\n\
            api Demozoo { rp_demozoo_get_heat(id: u32) -> DemozooHeat }";

        emit_src("list_of_option", src);
    }

    #[test]
    fn nesting_an_optional_record_by_value_reads_as_an_option() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            struct DemozooBadge { name: String, found: bool }\n\
            #[read]\n\
            struct DemozooAward { badge: DemozooBadge }\n\
            api Demozoo { rp_demozoo_get_award(id: u32) -> DemozooAward }";

        let emitted = emit_src("nested_option", src);
        assert!(emitted.contains(
            "pub unsafe fn read_demozoo_badge<'a>(raw: &abi::DemozooBadge) -> Option<Badge<'a>> {"
        ));
        assert!(emitted.contains("        badge: unsafe { read_demozoo_badge(&raw.badge) },"));
    }
}
