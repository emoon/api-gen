//! Host-side publish marshalling, emitted from the paired model: one file per def
//! carrying a publish fn per paired struct a slot returns, plus the all-zero miss
//! constant for each optional record.

use crate::api_parser::ApiDef;
use crate::emit_util::{
    group_imports, header, type_name, write_doc, write_signature, write_use_list,
};
use crate::pairing::{
    nested_enum, nested_record, nesting_order, slot_types, PairedModel, PairedStruct,
};
use heck::{ToShoutySnakeCase, ToSnakeCase};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{BufWriter, Write};

/// Where the emitted files reach for the types and helpers they use.
pub struct MarshalPaths<'a> {
    /// Crate holding the raw ABI modules: `<crate>::<def>` is aliased to abi.
    pub abi_crate: &'a str,
    /// Verbatim use paths the emitted code needs - the arena type, the
    /// string-into-arena type, the array-publishing helper.
    pub uses: &'a [String],
    /// Regeneration script named in the emitted header.
    pub script: &'a str,
}

/// Emit one module per def with publishable records, answering their module
/// names.
pub fn generate(
    dir: &str,
    publishable: &[String],
    model: &PairedModel,
    paths: &MarshalPaths,
) -> std::io::Result<Vec<String>> {
    report_skipped(model, publishable);

    let mut per_def: BTreeMap<&str, Vec<&PairedStruct>> = BTreeMap::new();
    for name in publishable {
        let paired = &model.structs[name];
        per_def.entry(&paired.def).or_default().push(paired);
    }

    let mut modules = Vec::new();
    for (def, structs) in &per_def {
        let module = format!("{}_marshal", def);
        write_module(dir, &module, def, structs, model, paths)?;
        modules.push(module);
    }
    Ok(modules)
}

/// The index the two emitted trees share: the publish modules, and the round-trip
/// tests that drive them.
pub fn write_mod_file(
    dir: &str,
    modules: &[String],
    tests: &[String],
    script: &str,
) -> std::io::Result<()> {
    let mut f = BufWriter::new(File::create(format!("{}/mod.rs", dir))?);
    writeln!(f, "{}", header(script))?;
    for module in modules {
        writeln!(f, "pub(crate) mod {};", module)?;
    }
    for module in tests {
        writeln!(f)?;
        writeln!(f, "#[cfg(test)]")?;
        writeln!(f, "mod {};", module)?;
    }
    Ok(())
}

/// Every struct a slot returns whose whole record lowers, each after everything it
/// nests: what generate emits, and what a round-trip test can pair against.
pub fn publishable(api_defs: &[ApiDef], model: &PairedModel) -> Vec<String> {
    emission_order(model, &slot_types(api_defs, model, true))
}

/// Every struct reachable from a root whose whole record lowers, each after
/// everything it nests. A record that does not lower takes what only it reaches
/// out with it.
fn emission_order(model: &PairedModel, roots: &BTreeSet<String>) -> Vec<String> {
    let mut lowers = BTreeMap::new();
    let lowering: Vec<&str> = roots
        .iter()
        .filter(|root| lowers_whole(model, root, &mut lowers))
        .map(String::as_str)
        .collect();
    nesting_order(model, lowering.into_iter(), |_| true)
}

/// Whether name and everything it nests publish without a hand-written body.
/// An optional record needs one more thing than the rest: an all-zero value for
/// every field, which a scalar the emitter cannot zero and a nested record with
/// no miss constant of its own do not have.
fn lowers_whole(model: &PairedModel, name: &str, seen: &mut BTreeMap<String, bool>) -> bool {
    if let Some(known) = seen.get(name) {
        return *known;
    }
    let Some(paired) = model.structs.get(name) else {
        return false;
    };
    // Assumed while descending, so a record that reaches itself terminates.
    seen.insert(name.to_owned(), true);
    let lowers = paired.dir.publish
        && paired.fields.iter().all(|field| {
            if field.with.is_some() {
                return false;
            }
            // A `[fixed]` field has no host counterpart, and no zero either: the
            // miss constant an optional record needs cannot name one.
            if field.fixed.is_some() {
                return !paired.found_synthesis;
            }
            // A list zeroes to a null pointer; anything else an optional record
            // carries needs a zero of its own.
            let in_list = field.count.is_some();
            match nested_record(model, field) {
                Some(ty) => {
                    lowers_whole(model, ty, seen)
                        && (!paired.found_synthesis || in_list || model.structs[ty].found_synthesis)
                }
                None => {
                    !paired.found_synthesis
                        || in_list
                        || field.ty == "String"
                        || zero_of(&field.ty).is_some()
                        || nested_enum(model, field).is_some_and(|e| e.zero.is_some())
                }
            }
        });
    seen.insert(name.to_owned(), lowers);
    lowers
}

/// Per record in the model, whether publishing it copies into an arena - a
/// string, a list, or a nested record that itself does. A record that copies
/// nothing publishes with no arena parameter and no unsafe, so every call site
/// naming it hands it none; all of them read their arity out of this one map.
///
/// Settled as a fixpoint rather than by descent because records may nest
/// cyclically: a descent has to answer for a record it is still deciding, and the
/// answer depends on which record the walk entered from. Copying only ever turns
/// on, so repeating until nothing changes lands on the same map from anywhere.
pub fn arena_use(model: &PairedModel) -> BTreeMap<String, bool> {
    let mut needs: BTreeMap<String, bool> = model
        .structs
        .keys()
        .map(|name| (name.clone(), false))
        .collect();
    loop {
        let mut changed = false;
        for (name, paired) in &model.structs {
            if needs[name] {
                continue;
            }
            let copies = paired.fields.iter().any(|field| {
                field.ty == "String"
                    || field.count.is_some()
                    || nested_record(model, field).is_some_and(|ty| needs[ty])
            });
            if copies {
                needs.insert(name.clone(), true);
                changed = true;
            }
        }
        if !changed {
            return needs;
        }
    }
}

fn report_skipped(model: &PairedModel, emitted: &[String]) {
    let skipped: Vec<&str> = model
        .structs
        .values()
        .filter(|s| s.dir.publish && !emitted.contains(&s.name))
        .map(|s| s.name.as_str())
        .collect();
    if !skipped.is_empty() {
        println!(
            "api_gen: marshal: {} record(s) still hand-published: {}",
            skipped.len(),
            skipped.join(", ")
        );
    }
}

fn write_module(
    dir: &str,
    module: &str,
    def: &str,
    structs: &[&PairedStruct],
    model: &PairedModel,
    paths: &MarshalPaths,
) -> std::io::Result<()> {
    let mut f = BufWriter::new(File::create(format!("{}/{}.rs", dir, module))?);

    let arena = arena_use(model);

    writeln!(f, "{}", header(paths.script))?;
    writeln!(
        f,
        "//! Arena marshalling for {}.def's view-paired records.",
        def
    )?;
    // A def whose every record is scalar copies nothing and emits no unsafe, so it
    // gets no allow either.
    if structs.iter().any(|s| arena[&s.name]) {
        writeln!(f, "//!")?;
        writeln!(
            f,
            "//! SAFETY: a publish fn taking an arena requires it live for the call - its"
        )?;
        writeln!(
            f,
            "//! stated contract - and every unsafe block is a copy into that arena."
        )?;
        writeln!(f, "#![allow(clippy::undocumented_unsafe_blocks)]")?;
        writeln!(f, "#![allow(unsafe_code)]")?;
    }
    writeln!(f)?;

    let mut body = Vec::new();
    for paired in structs {
        if paired.found_synthesis {
            write_miss_const(&mut body, paired, model)?;
        }
        write_publish(&mut body, paired, model, &arena)?;
    }
    let body = String::from_utf8(body).expect("the emitter writes UTF-8");

    // A def with no string field never names RawStr, and one with no list never
    // names publish_array: an import the module does not use is a hard error in
    // the consumer's lane.
    for path in paths.uses.iter().filter(|p| body.contains(type_name(p))) {
        writeln!(f, "use {};", path)?;
    }
    writeln!(f)?;
    writeln!(f, "use {}::{} as abi;", paths.abi_crate, def)?;
    writeln!(f)?;
    for (module, types) in group_imports(structs.iter().map(|s| s.view.as_str())) {
        write_use_list(&mut f, module, &types)?;
    }
    write!(f, "{}", body)
}

fn write_miss_const(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
) -> std::io::Result<()> {
    writeln!(f)?;
    write_doc(
        f,
        &format!(
            "The `{}` a missing `{}` publishes: every pointer null, every string empty, \
             `found` clear.",
            paired.name,
            view_type(paired)
        ),
    )?;
    writeln!(
        f,
        "pub(crate) const {}: abi::{} = abi::{} {{",
        miss_const(&paired.name),
        paired.name,
        paired.name
    )?;
    for field in &paired.fields {
        let zero = if let Some(count) = &field.count {
            writeln!(f, "    {}: core::ptr::null(),", field.name)?;
            writeln!(f, "    {}: 0,", count)?;
            continue;
        } else if field.ty == "String" {
            "RawStr::EMPTY".to_owned()
        } else if let Some(ty) = nested_record(model, field) {
            miss_const(ty)
        } else if let Some(paired_enum) = nested_enum(model, field) {
            let zero = paired_enum.zero.as_ref().unwrap_or_else(|| {
                panic!(
                    "api_gen: `{}.{}` crosses as `{}`, which declares no zero variant",
                    paired.name, field.name, field.ty
                )
            });
            format!("abi::{}::{}", field.ty, zero)
        } else {
            zero_of(&field.ty).unwrap_or_else(|| {
                panic!(
                    "api_gen: `{}.{}` crosses as `{}`, which has no known zero",
                    paired.name, field.name, field.ty
                )
            })
        };
        writeln!(f, "    {}: {},", field.name, zero)?;
    }
    writeln!(f, "    found: false,")?;
    writeln!(f, "}};")?;
    Ok(())
}

fn write_publish(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
    arena: &BTreeMap<String, bool>,
) -> std::io::Result<()> {
    let view = view_type(paired);
    let arrays: Vec<&_> = paired.fields.iter().filter(|f| f.count.is_some()).collect();
    let takes_arena = arena[&paired.name];
    // A nested publish that copies nothing takes no arena, so the call naming it
    // passes none and needs no unsafe.
    let nested_call = |ty: &str, arg: String| {
        if arena[ty] {
            format!("unsafe {{ {}({}, arena) }}", publish_fn(ty), arg)
        } else {
            format!("{}({})", publish_fn(ty), arg)
        }
    };

    writeln!(f)?;
    let doc = if paired.found_synthesis {
        format!(
            "Publish a [`{}`] as an abi::{} with found set; a missing view publishes [`{}`].",
            view,
            paired.name,
            miss_const(&paired.name)
        )
    } else {
        format!("Publish a [`{}`] as an abi::{}.", view, paired.name)
    };
    write_doc(f, &doc)?;
    let mut params = vec![format!("view: &{}", view)];
    if takes_arena {
        writeln!(f, "///")?;
        writeln!(f, "/// # Safety")?;
        writeln!(f, "/// arena must be a live arena for the call.")?;
        params.push("arena: *mut FlArena".to_owned());
    }
    write_signature(
        f,
        &format!(
            "pub(crate) {}fn {}(",
            if takes_arena { "unsafe " } else { "" },
            publish_fn(&paired.name)
        ),
        &params,
        &format!(") -> abi::{} {{", paired.name),
    )?;

    for field in &arrays {
        let count = field.count.as_ref().expect("an array field is fused");
        let lower = match nested_record(model, field) {
            Some(ty) if arena[ty] => format!(
                "|item, arena| {{\n            {}(item, arena)\n        }}",
                publish_fn(ty)
            ),
            Some(ty) => format!("|item, _| {}(item)", publish_fn(ty)),
            None => "|item, _| *item".to_owned(),
        };
        writeln!(f, "    let ({}, {}) = unsafe {{", field.name, count)?;
        writeln!(
            f,
            "        publish_array(&view.{}, arena, {})",
            field.host, lower
        )?;
        writeln!(f, "    }};")?;
    }

    writeln!(f, "    abi::{} {{", paired.name)?;
    for field in &paired.fields {
        if let Some(count) = &field.count {
            writeln!(f, "        {},", field.name)?;
            writeln!(f, "        {},", count)?;
        } else if field.ty == "String" {
            writeln!(
                f,
                "        {}: unsafe {{ RawStr::in_arena(arena, &view.{}) }},",
                field.name, field.host
            )?;
        } else if let Some(ty) = nested_record(model, field) {
            // An optional record is held as an Option, and its absent arm is the
            // miss constant rather than a zeroed record with found set.
            if model.structs[ty].found_synthesis {
                writeln!(f, "        {}: match &view.{} {{", field.name, field.host)?;
                writeln!(
                    f,
                    "            Some(view) => {},",
                    nested_call(ty, "view".to_owned())
                )?;
                writeln!(f, "            None => {},", miss_const(ty))?;
                writeln!(f, "        }},")?;
            } else {
                writeln!(
                    f,
                    "        {}: {},",
                    field.name,
                    nested_call(ty, format!("&view.{}", field.host))
                )?;
            }
        } else if let Some(value) = &field.fixed {
            writeln!(f, "        {}: abi::{}::{},", field.name, field.ty, value)?;
        } else {
            writeln!(f, "        {}: view.{},", field.name, field.host)?;
        }
    }
    if paired.found_synthesis {
        writeln!(f, "        found: true,")?;
    }
    writeln!(f, "    }}")?;
    writeln!(f, "}}")?;
    Ok(())
}

/// The all-zero value of a scalar the IDL can spell.
pub fn zero_of(ty: &str) -> Option<String> {
    match ty {
        "bool" => Some("false".to_owned()),
        "f32" | "f64" => Some("0.0".to_owned()),
        "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" => Some("0".to_owned()),
        _ => None,
    }
}

fn view_type(paired: &PairedStruct) -> &str {
    type_name(&paired.view)
}

pub fn publish_fn(name: &str) -> String {
    format!("publish_{}", name.to_snake_case())
}

pub fn miss_const(name: &str) -> String {
    format!("NO_{}", name.to_shouty_snake_case())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::ApiParser;

    /// Every shape the emitter lowers, and every shape it refuses. DemozooProduction
    /// nests a plain record inside an optional one, DemozooReleaser a `[with]` field;
    /// neither publishes, and DemozooAuthor - reachable from nowhere else - goes with
    /// them. An enum copies like a scalar, but only when it declares a zero variant for
    /// the miss constant to name, which DemozooTier does not.
    const DEMOZOO: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        extern opaque FlArena\n\
        enum DemozooSupertype { Any, Production }\n\
        enum DemozooVolume {\n\
            Loud = 1,\n\
            Quiet = 0,\n\
        }\n\
        struct DemozooCard {\n\
            name: String,\n\
            supertype: DemozooSupertype,\n\
            volume: DemozooVolume,\n\
            found: bool,\n\
        }\n\
        enum DemozooTier {\n\
            Gold = 1,\n\
            Silver = 2,\n\
        }\n\
        struct DemozooSeat { tier: DemozooTier, found: bool }\n\
        struct DemozooAuthor { name: String }\n\
        struct DemozooProduction {\n\
            title: String,\n\
            supertype: DemozooSupertype,\n\
            author: DemozooAuthor,\n\
            found: bool,\n\
        }\n\
        struct DemozooReleaser {\n\
            [with(crate::demozoo_abi::read_name)] name: String,\n\
        }\n\
        struct DemozooPlacingEntry { production_id: u32, position: u16 }\n\
        struct DemozooPlacing { position: u16, found: bool }\n\
        struct DemozooBadge { name: String }\n\
        struct DemozooAward { badge: DemozooBadge, found: bool }\n\
        struct DemozooEntry { best: DemozooPlacing }\n\
        struct DemozooStamp { code: u16 }\n\
        struct DemozooTicket { stamp: DemozooStamp }\n\
        struct DemozooPoster { sheet: DemozooSheet }\n\
        struct DemozooSheet { text: String }\n\
        struct DemozooFolio { card: DemozooCard }\n\
        struct DemozooChain { links: *const DemozooChain, link_count: u32 }\n\
        struct DemozooHolder { owners: *const DemozooLoop, owner_count: u32 }\n\
        struct DemozooLoop { holder: DemozooHolder }\n\
        struct DemozooTags { ids: *const u32, id_count: u32 }\n\
        enum DemozooState {\n\
            Idle = 0,\n\
            Ready = 1,\n\
        }\n\
        struct DemozooSlot {\n\
            [fixed(Ready)] state: DemozooState,\n\
            code: u16,\n\
        }\n\
        struct DemozooLease {\n\
            [fixed(Ready)] state: DemozooState,\n\
            found: bool,\n\
        }\n\
        struct DemozooCompetition {\n\
            name: String,\n\
            placings: *const DemozooPlacingEntry,\n\
            placing_count: u32,\n\
        }\n\
        struct DemozooPartyDetail {\n\
            name: String,\n\
            rating: f32,\n\
            competitions: *const DemozooCompetition,\n\
            competition_count: u32,\n\
            soundtracks: *const u32,\n\
            soundtrack_count: u32,\n\
            best: DemozooPlacing,\n\
            found: bool,\n\
        }\n\
        api Demozoo {\n\
            rp_demozoo_get_production(id: u32, arena: *FlArena) -> DemozooProduction\n\
            rp_demozoo_get_releaser(id: u32, arena: *FlArena) -> DemozooReleaser\n\
            rp_demozoo_get_award(id: u32, arena: *FlArena) -> DemozooAward\n\
            rp_demozoo_get_entry(id: u32, arena: *FlArena) -> DemozooEntry\n\
            rp_demozoo_get_ticket(id: u32, arena: *FlArena) -> DemozooTicket\n\
            rp_demozoo_get_tags(id: u32, arena: *FlArena) -> DemozooTags\n\
            rp_demozoo_get_slot(id: u32, arena: *FlArena) -> DemozooSlot\n\
            rp_demozoo_get_lease(id: u32, arena: *FlArena) -> DemozooLease\n\
            rp_demozoo_get_party_detail(id: u32, arena: *FlArena) -> DemozooPartyDetail\n\
            rp_demozoo_get_card(id: u32, arena: *FlArena) -> DemozooCard\n\
            rp_demozoo_get_seat(id: u32, arena: *FlArena) -> DemozooSeat\n\
            rp_demozoo_get_poster(id: u32, arena: *FlArena) -> DemozooPoster\n\
            rp_demozoo_get_folio(id: u32, arena: *FlArena) -> DemozooFolio\n\
            rp_demozoo_get_chain(id: u32, arena: *FlArena) -> DemozooChain\n\
            rp_demozoo_get_loop(id: u32, arena: *FlArena) -> DemozooLoop\n\
        }";

    /// A def carrying nothing an arena is needed for.
    const SCALARS: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        extern opaque FlArena\n\
        struct DemozooStamp { code: u16 }\n\
        api Demozoo { rp_demozoo_get_stamp(id: u32, arena: *FlArena) -> DemozooStamp }";

    /// Generate DEMOZOO into a temp dir and answer the emitted marshal file.
    fn emit(tag: &str) -> String {
        emit_src(tag, DEMOZOO)
    }

    fn emit_src(tag: &str, src: &str) -> String {
        let dir =
            std::env::temp_dir().join(format!("api_gen_marshal_{}_{}", std::process::id(), tag));
        std::fs::create_dir_all(&dir).expect("create temp dir");

        let mut api_def = crate::api_parser::ApiDef::default();
        ApiParser::parse_string(src, "demozoo.def", &mut api_def);
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);
        let model = crate::pairing::resolve(&api_defs).expect("pairs");

        generate(
            dir.to_str().unwrap(),
            &publishable(&api_defs, &model),
            &model,
            &MarshalPaths {
                abi_crate: "replay_plugin",
                uses: &["crate::catalog_abi::publish_array".to_owned()],
                script: "scripts/gen.sh",
            },
        )
        .expect("generate");

        let emitted =
            std::fs::read_to_string(dir.join("demozoo_marshal.rs")).expect("read emitted");
        let _ = std::fs::remove_dir_all(&dir);
        emitted
    }

    #[test]
    fn a_nested_record_is_published_before_the_record_that_nests_it() {
        let emitted = emit("nesting");

        let entry = emitted
            .find("fn publish_demozoo_placing_entry")
            .expect("entry");
        let competition = emitted
            .find("fn publish_demozoo_competition")
            .expect("competition");
        let detail = emitted
            .find("fn publish_demozoo_party_detail")
            .expect("detail");
        assert!(entry < competition && competition < detail);

        assert!(emitted.contains(
            "    let (competitions, competition_count) = unsafe {\n\
             \x20       publish_array(&view.competitions, arena, |item, arena| {\n\
             \x20           publish_demozoo_competition(item, arena)\n\
             \x20       })\n\
             \x20   };"
        ));
    }

    /// A list of scalars copies its elements; an optional record nested by value is
    /// held as an Option, whose absent arm is that record's miss constant.
    #[test]
    fn a_scalar_list_and_a_by_value_record_lower_too() {
        let emitted = emit("field_shapes");

        assert!(emitted.contains("publish_array(&view.soundtracks, arena, |item, _| *item)"));
        assert!(emitted.contains(
            "        best: match &view.best {\n\
             \x20           Some(view) => publish_demozoo_placing(view),\n\
             \x20           None => NO_DEMOZOO_PLACING,\n\
             \x20       },"
        ));
        // A record that is not optional is held by value and copies straight.
        assert!(emitted.contains("stamp: publish_demozoo_stamp(&view.stamp),"));
        // The same arm when the nested record does copy: both arities of the
        // optional form are pinned, so neither can drift onto the other.
        assert!(emitted.contains(
            "        card: match &view.card {\n\
             \x20           Some(view) => unsafe { publish_demozoo_card(view, arena) },\n\
             \x20           None => NO_DEMOZOO_CARD,\n\
             \x20       },"
        ));
    }

    #[test]
    fn a_record_that_reaches_itself_terminates_and_names_an_arena() {
        assert!(emit("cycle").contains(
            "pub(crate) unsafe fn publish_demozoo_chain(\n\
             \x20   view: &ChainView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooChain {"
        ));
    }

    /// The cycle that spans two records, where the list closing it sits on the other
    /// one. The record whose own fields copy nothing is the one an answer that
    /// descends gets wrong, leaving its body passing an arena its signature never
    /// took.
    #[test]
    fn a_cycle_spanning_two_records_names_an_arena_on_both() {
        let emitted = emit("mutual_cycle");

        assert!(emitted.contains(
            "pub(crate) unsafe fn publish_demozoo_loop(\n\
             \x20   view: &LoopView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooLoop {\n\
             \x20   abi::DemozooLoop {\n\
             \x20       holder: unsafe { publish_demozoo_holder(&view.holder, arena) },"
        ));
        assert!(emitted.contains(
            "pub(crate) unsafe fn publish_demozoo_holder(\n\
             \x20   view: &HolderView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooHolder {"
        ));
    }

    #[test]
    fn a_record_of_only_scalars_takes_no_arena() {
        assert!(emit("scalar_only").contains(
            "/// Publish a [`StampView`] as an abi::DemozooStamp.\n\
             pub(crate) fn publish_demozoo_stamp(view: &StampView) -> abi::DemozooStamp {\n\
             \x20   abi::DemozooStamp {\n\
             \x20       code: view.code,\n\
             \x20   }\n\
             }"
        ));
    }

    #[test]
    fn a_record_holding_a_string_names_its_arena() {
        assert!(emit("string_arena").contains(
            "pub(crate) unsafe fn publish_demozoo_sheet(\n\
             \x20   view: &SheetView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooSheet {"
        ));
    }

    #[test]
    fn a_list_of_arena_free_records_publishes_each_without_one() {
        assert!(emit("arena_free_list").contains(
            "publish_array(&view.placings, arena, |item, _| publish_demozoo_placing_entry(item))"
        ));
    }

    #[test]
    fn a_module_with_no_arena_copy_carries_no_unsafe_allows() {
        let emitted = emit_src("no_unsafe", SCALARS);

        assert!(!emitted.contains("unsafe"));
        assert!(!emitted.contains("allow("));
        assert!(!emitted.contains("# Safety"));
        // The def that does copy still says so.
        assert!(emit("unsafe_allows").contains("#![allow(unsafe_code)]"));
    }

    /// A `[fixed]` field has no host counterpart, and no zero either - so an optional
    /// record carrying one has nothing to spell in its miss constant.
    #[test]
    fn a_fixed_field_publishes_the_variant_it_names() {
        let emitted = emit("fixed");

        assert!(emitted.contains("        state: abi::DemozooState::Ready,"));
        assert!(!emitted.contains("view.state"));
        assert!(!emitted.contains("publish_demozoo_lease"));
    }

    #[test]
    fn an_import_the_module_does_not_use_is_left_out() {
        let emitted = emit("imports");

        assert!(emitted.contains("use crate::catalog_abi::publish_array;"));
        assert!(!emit_src("no_imports", SCALARS).contains("use crate::catalog_abi::publish_array;"));
    }

    #[test]
    fn an_optional_record_gets_a_miss_constant_and_sets_found() {
        let emitted = emit("found");

        assert!(
            emitted.contains("pub(crate) const NO_DEMOZOO_PARTY_DETAIL: abi::DemozooPartyDetail")
        );
        assert!(emitted.contains("    name: RawStr::EMPTY,\n    rating: 0.0,"));
        assert!(emitted.contains("    competitions: core::ptr::null(),\n    competition_count: 0,"));
        assert!(emitted.contains("    best: NO_DEMOZOO_PLACING,\n    found: false,"));
        assert!(emitted.contains("        found: true,"));
    }

    #[test]
    fn a_record_without_found_gets_no_miss_constant() {
        assert!(!emit("no_found").contains("NO_DEMOZOO_COMPETITION"));
    }

    /// A field the emitter cannot lower - a plain record inside an optional one, or
    /// one handed to a host helper - keeps its record hand-written, and takes what only
    /// it reaches with it.
    #[test]
    fn a_record_the_emitter_cannot_lower_is_not_emitted() {
        let emitted = emit("skipped");

        assert!(!emitted.contains("publish_demozoo_production"));
        assert!(!emitted.contains("publish_demozoo_releaser"));
        assert!(!emitted.contains("publish_demozoo_author"));
    }

    /// A record with no found of its own has no miss constant for the optional
    /// record nesting it to name.
    #[test]
    fn an_optional_record_nesting_a_plain_record_by_value_is_not_emitted() {
        let emitted = emit("no_nested_miss");

        assert!(!emitted.contains("publish_demozoo_award"));
        assert!(!emitted.contains("publish_demozoo_badge"));
    }

    /// An enum copies like a scalar and zeroes to the variant valued zero - found by
    /// value, not by position: DemozooVolume spells its zero second. DemozooTier
    /// declares no zero at all, so the optional record carrying it is refused.
    #[test]
    fn an_enum_field_copies_and_zeroes_to_its_zero_variant() {
        let emitted = emit("enum_field");

        assert!(emitted.contains("        supertype: view.supertype,"));
        assert!(emitted.contains("        volume: view.volume,"));
        assert!(emitted.contains("    supertype: abi::DemozooSupertype::Any,"));
        assert!(emitted.contains("    volume: abi::DemozooVolume::Quiet,"));
        assert!(!emitted.contains("publish_demozoo_seat"));
    }

    #[test]
    fn a_record_that_only_holds_a_list_names_its_arena() {
        assert!(emit("list_arena").contains(
            "pub(crate) unsafe fn publish_demozoo_tags(\n\
             \x20   view: &TagsView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooTags {"
        ));
    }

    /// The index allows no dead_code: an emitted publish nothing calls is the
    /// signal that a crossing was never wired up.
    #[test]
    fn the_index_declares_the_publish_modules_and_the_tests() {
        let dir = std::env::temp_dir().join(format!("api_gen_marshal_mod_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");

        write_mod_file(
            dir.to_str().unwrap(),
            &["demozoo_marshal".to_owned()],
            &["demozoo_roundtrip".to_owned()],
            "scripts/gen.sh",
        )
        .expect("write index");
        let emitted = std::fs::read_to_string(dir.join("mod.rs")).expect("read index");
        let _ = std::fs::remove_dir_all(&dir);

        assert_eq!(
            emitted,
            "// @generated by api_gen - DO NOT EDIT. Regenerate with scripts/gen.sh.\n\
             \n\
             pub(crate) mod demozoo_marshal;\n\
             \n\
             #[cfg(test)]\n\
             mod demozoo_roundtrip;\n"
        );
    }

    /// Whether a record names an arena follows what it nests, all the way down.
    ///
    /// Poster sorts before Sheet, so the walk meets it first and only a second
    /// pass settles it - rename either and this stops pinning that the fixpoint
    /// re-iterates at all.
    #[test]
    fn a_record_names_an_arena_when_what_it_nests_needs_one() {
        let emitted = emit("arena_naming");

        assert!(emitted.contains(
            "pub(crate) unsafe fn publish_demozoo_poster(\n\
             \x20   view: &PosterView,\n\
             \x20   arena: *mut FlArena,\n\
             ) -> abi::DemozooPoster {\n\
             \x20   abi::DemozooPoster {\n\
             \x20       sheet: unsafe { publish_demozoo_sheet(&view.sheet, arena) },"
        ));
        assert!(emitted.contains(
            "pub(crate) fn publish_demozoo_entry(view: &EntryView) -> abi::DemozooEntry"
        ));
    }
}
