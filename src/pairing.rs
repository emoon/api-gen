//! View pairing: which host type each def type marshals to, and how their fields
//! line up. Resolution only.
//!
//! `#[reads(<plugin module path>)]` is the same pairing on the consume side:
//! `<DefPrefix><Name>` pairs with `<path>::<Name>`, and `#[read]` on a type is
//! what makes a reader emit for it.
//!
//! A def opts in with `#[views(<host module path>)]`, after which
//! `<DefPrefix><Name>` pairs with `<path>::<Name>View`, the def prefix being the
//! `#[module]` name in upper camel case. `#[view(<path>)]` on a type is the
//! exception hatch. Direction comes from position: a type reached from a return
//! publishes view -> ABI, from a parameter it reads ABI -> host, and a nested
//! field type inherits it.
//!
//! Host paths are taken verbatim - nothing here knows whether they resolve. A
//! mispairing surfaces as a rustc error in the generated code.

use crate::api_parser::{zero_variant, ApiDef, Enum, EnumType, Struct, Variable};
use heck::ToUpperCamelCase;
use std::collections::{BTreeMap, BTreeSet};

/// Which way a paired type crosses. Both are set for a type used in both positions.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Direction {
    pub publish: bool,
    pub read: bool,
}

/// One ABI field and the host field it pairs with.
#[derive(Debug)]
pub struct PairedField {
    pub name: String,
    /// The host field's name - `[from(...)]` when renamed, else name.
    pub host: String,
    /// The def type this field carries (String, u32, a def type name).
    pub ty: String,
    /// The u32 count field fused with this pointer field.
    pub count: Option<String>,
    /// `[with(<helper path>)]`: the host helper that marshals this field whole.
    pub with: Option<String>,
    /// `[read_with(<helper path>)]`: the consume-side helper that reads it whole.
    pub read_with: Option<String>,
    /// `[fixed(<value>)]`: no host counterpart - every publish writes this value.
    pub fixed: Option<String>,
    /// The def type this field's value pairs through, when it names one.
    pub nested: Option<String>,
}

#[derive(Debug)]
pub struct PairedStruct {
    pub name: String,
    /// Base filename of the def that declares this type.
    pub def: String,
    pub view: String,
    /// The consume-side type read back from this record, when its def carries
    /// `#[reads(...)]`.
    pub owned: Option<String>,
    /// `#[read]`: a reader emits for this record, and for everything it nests.
    pub read_root: bool,
    pub dir: Direction,
    pub fields: Vec<PairedField>,
    /// A found: bool field with no host counterpart: the record publishes from
    /// `Option<View>`, and found is synthesized from which arm it was.
    pub found_synthesis: bool,
}

#[derive(Debug)]
pub struct PairedVariant {
    pub name: String,
    pub host: String,
}

#[derive(Debug)]
pub struct PairedEnum {
    pub name: String,
    pub view: String,
    /// The variant a value the def never declared decodes to. The read emitter
    /// requires it; an enum that only publishes has nothing undeclared to decode.
    pub fallback: Option<String>,
    /// The variant valued zero, which is what an optional record's miss constant
    /// spells for a field of this type.
    pub zero: Option<String>,
    /// `#[attributes(packed)]`: the enum crosses as one byte rather than as the C
    /// default, which is the integer an inbound read decodes from.
    pub packed: bool,
    pub dir: Direction,
    pub variants: Vec<PairedVariant>,
}

/// The paired records a slot names by value: from its return when publish, from
/// its parameters otherwise.
pub fn slot_types(api_defs: &[ApiDef], model: &PairedModel, publish: bool) -> BTreeSet<String> {
    let mut roots = BTreeSet::new();
    for api_def in api_defs {
        for api in &api_def.apis {
            for func in &api.functions {
                let named: Vec<&str> = if publish {
                    func.return_val
                        .iter()
                        .map(|v| v.type_name.as_str())
                        .collect()
                } else {
                    func.function_args
                        .iter()
                        .map(|a| a.type_name.as_str())
                        .collect()
                };
                for name in named {
                    if model.structs.contains_key(name) {
                        roots.insert(name.to_owned());
                    }
                }
            }
        }
    }
    roots
}

/// Every record reachable from roots through the fields follow accepts, each
/// after the records it nests. A record can reach itself through a pointer list,
/// so a name already walked is skipped rather than walked again.
pub fn nesting_order<'a>(
    model: &PairedModel,
    roots: impl Iterator<Item = &'a str>,
    follow: impl Fn(&PairedField) -> bool,
) -> Vec<String> {
    fn walk(
        model: &PairedModel,
        name: &str,
        follow: &impl Fn(&PairedField) -> bool,
        seen: &mut BTreeSet<String>,
        order: &mut Vec<String>,
    ) {
        if !seen.insert(name.to_owned()) {
            return;
        }
        for field in model.structs[name].fields.iter().filter(|f| follow(f)) {
            if let Some(ty) = nested_record(model, field) {
                walk(model, ty, follow, seen, order);
            }
        }
        order.push(name.to_owned());
    }

    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    for root in roots {
        walk(model, root, &follow, &mut seen, &mut order);
    }
    order
}

/// The record a field's value pairs through, when it is a record rather than an
/// enum.
pub fn nested_record<'a>(model: &'a PairedModel, field: &'a PairedField) -> Option<&'a str> {
    field
        .nested
        .as_deref()
        .filter(|ty| model.structs.contains_key(*ty))
}

/// The enum a field's value pairs through, when it is one rather than a record.
/// An enum crosses as its own variant on both sides, so it copies like a scalar.
pub fn nested_enum<'a>(model: &'a PairedModel, field: &'a PairedField) -> Option<&'a PairedEnum> {
    field.nested.as_deref().and_then(|ty| model.enums.get(ty))
}

#[derive(Debug, Default)]
pub struct PairedModel {
    pub structs: BTreeMap<String, PairedStruct>,
    pub enums: BTreeMap<String, PairedEnum>,
}

/// Def types that can pair, by name. Only types declared by a def that opts into
/// pairing are here. Handles, opaques, field-less structs and bitflags sets are
/// excluded too: a handle crosses as its integer, a bitflags set is the host
/// vocabulary, and the rest have no fields to pair.
struct Index<'a> {
    structs: BTreeMap<&'a str, (&'a Struct, &'a ApiDef)>,
    enums: BTreeMap<&'a str, (&'a Enum, &'a ApiDef)>,
}

impl<'a> Index<'a> {
    fn build(api_defs: &'a [ApiDef]) -> Self {
        let mut structs = BTreeMap::new();
        let mut enums = BTreeMap::new();

        for api_def in api_defs.iter().filter(|d| pairs_types(d)) {
            for sdef in &api_def.structs {
                if sdef.is_handle_type || sdef.is_opaque() || sdef.variables.is_empty() {
                    continue;
                }
                structs.insert(sdef.name.as_str(), (sdef, api_def));
            }
            for edef in &api_def.enums {
                if edef.enum_type == EnumType::Bitflags {
                    continue;
                }
                enums.insert(edef.name.as_str(), (edef, api_def));
            }
        }

        Index { structs, enums }
    }

    fn contains(&self, name: &str) -> bool {
        self.structs.contains_key(name) || self.enums.contains_key(name)
    }
}

/// Pair every def type that crosses a pairing def's api slot, and everything
/// they nest. A def that carries no pairing annotation at all pairs nothing.
pub fn resolve(api_defs: &[ApiDef]) -> Result<PairedModel, String> {
    let index = Index::build(api_defs);
    let mut dirs: BTreeMap<String, Direction> = BTreeMap::new();

    for api_def in api_defs.iter().filter(|d| pairs_types(d)) {
        for api in &api_def.apis {
            for func in &api.functions {
                if let Some(ret) = &func.return_val {
                    visit(&index, &ret.type_name, true, &mut dirs);
                }
                for arg in &func.function_args {
                    visit(&index, &arg.type_name, false, &mut dirs);
                }
            }
        }
    }

    let mut model = PairedModel::default();
    for (name, dir) in &dirs {
        if let Some((sdef, api_def)) = index.structs.get(name.as_str()) {
            let paired = pair_struct(&index, sdef, api_def, *dir)?;
            model.structs.insert(name.clone(), paired);
        } else if let Some((edef, api_def)) = index.enums.get(name.as_str()) {
            let paired = pair_enum(edef, api_def, *dir)?;
            model.enums.insert(name.clone(), paired);
        }
    }

    Ok(model)
}

/// Whether this def opts into pairing: `#[views(...)]`, or a `#[view(...)]` hatch
/// on one of its types. A def that names a paired type from another def is pulled
/// in through the nesting walk instead.
fn pairs_types(api_def: &ApiDef) -> bool {
    api_def.views.is_some()
        || api_def.reads.is_some()
        || api_def.structs.iter().any(|s| s.view.is_some() || s.read)
        || api_def.enums.iter().any(|e| e.view.is_some())
}

/// Record name's direction and descend into the types its fields name.
fn visit(index: &Index, name: &str, publish: bool, dirs: &mut BTreeMap<String, Direction>) {
    if !index.contains(name) {
        return;
    }

    let dir = dirs.entry(name.to_owned()).or_default();
    let seen = if publish { dir.publish } else { dir.read };
    if seen {
        return;
    }
    if publish {
        dir.publish = true;
    } else {
        dir.read = true;
    }

    if let Some((sdef, _)) = index.structs.get(name) {
        // A `[fixed]` field's type never pairs: the publish writes an ABI value
        // directly and the consume side copies it back as itself.
        for var in sdef.variables.iter().filter(|v| v.fixed.is_none()) {
            visit(index, &var.type_name, publish, dirs);
        }
    }
}

fn pair_struct(
    index: &Index,
    sdef: &Struct,
    api_def: &ApiDef,
    dir: Direction,
) -> Result<PairedStruct, String> {
    let view = view_path(
        sdef.view.as_ref().map(|v| v.path.as_str()),
        &sdef.name,
        api_def,
    )?;
    let mut fields = Vec::new();
    let mut found_synthesis = false;
    let mut i = 0;

    while i < sdef.variables.len() {
        let var = &sdef.variables[i];
        i += 1;

        // A bare found: bool is the publish-from-Option marker; `[from(...)]`
        // on it means the view really does carry the field.
        if var.name == "found" && var.type_name == "bool" && var.from_host.is_none() {
            found_synthesis = true;
            continue;
        }

        if var.fixed.is_some() && !index.enums.contains_key(var.type_name.as_str()) {
            return Err(format!(
                "api_gen: `{}.{}` is `[fixed(...)]` but crosses as `{}`; the marker names a \
                 variant, so the field must cross as a def enum",
                sdef.name, var.name, var.type_name
            ));
        }

        let mut count = None;
        if var.pointer || var.const_pointer {
            let partner = sdef.variables.get(i).filter(|v| is_count_for(v, &var.name));
            let partner = partner.ok_or_else(|| {
                format!(
                    "api_gen: `{}.{}` is a pointer with no count partner: expected a following \
                     `u32` named `{}_count` or `count`",
                    sdef.name, var.name, var.name
                )
            })?;
            count = Some(partner.name.clone());
            i += 1;
        }

        fields.push(PairedField {
            name: var.name.clone(),
            host: var.from_host.clone().unwrap_or_else(|| var.name.clone()),
            ty: var.type_name.clone(),
            count,
            with: var.with_helper.clone(),
            read_with: var.read_with.clone(),
            fixed: var.fixed.clone(),
            nested: index
                .contains(&var.type_name)
                .then(|| var.type_name.clone()),
        });
    }

    // A hatched type whose name is outside the def prefix pairs a view but has no
    // consume-side name to build. The read emitter is what refuses.
    let owned = api_def
        .reads
        .as_deref()
        .and_then(|reads| match &sdef.read_owned {
            Some(name) => Some(format!("{}::{}", reads, name)),
            None => stem(&sdef.name, api_def)
                .ok()
                .map(|stem| format!("{}::{}", reads, stem)),
        });

    Ok(PairedStruct {
        name: sdef.name.clone(),
        def: api_def.base_filename.clone(),
        view,
        owned,
        read_root: sdef.read,
        dir,
        fields,
        found_synthesis,
    })
}

fn pair_enum(edef: &Enum, api_def: &ApiDef, dir: Direction) -> Result<PairedEnum, String> {
    let spec = edef.view.as_ref();
    let view = view_path(spec.map(|v| v.path.as_str()), &edef.name, api_def)?;
    let fallback = spec.and_then(|v| v.fallback.clone());

    let variants = edef
        .entries
        .iter()
        .map(|e| PairedVariant {
            name: e.name.clone(),
            host: e.from_host.clone().unwrap_or_else(|| e.name.clone()),
        })
        .collect();

    let zero = zero_variant(edef).map(str::to_owned);

    Ok(PairedEnum {
        name: edef.name.clone(),
        view,
        fallback,
        zero,
        packed: edef.is_packed,
        dir,
        variants,
    })
}

/// The host type name pairs with: the `#[view(...)]` hatch, else the convention.
fn view_path(hatch: Option<&str>, name: &str, api_def: &ApiDef) -> Result<String, String> {
    if let Some(path) = hatch {
        return Ok(path.to_owned());
    }

    let views = api_def.views.as_ref().ok_or_else(|| {
        format!(
            "api_gen: `{}` in `{}.def` pairs by convention but the def declares no \
             `#[views(<host module path>)]`",
            name, api_def.base_filename
        )
    })?;

    Ok(format!("{}::{}View", views, stem(name, api_def)?))
}

/// name with the def prefix cut off - what both pairing conventions build on.
fn stem<'a>(name: &'a str, api_def: &ApiDef) -> Result<&'a str, String> {
    let prefix = api_def.module.to_upper_camel_case();
    name.strip_prefix(&prefix).ok_or_else(|| {
        format!(
            "api_gen: `{}` in `{}.def` does not start with the def prefix `{}`, so it cannot pair \
             by convention: name it `{}<Name>` or give it `#[view(<path>)]`",
            name, api_def.base_filename, prefix, prefix
        )
    })
}

/// Whether var is the count partner of the pointer field ptr_name. A list
/// counts its elements, so the singular stem (placings / placing_count) is
/// spelled as often as the plural.
fn is_count_for(var: &Variable, ptr_name: &str) -> bool {
    let singular = ptr_name.strip_suffix('s').unwrap_or(ptr_name);
    var.type_name == "u32"
        && !var.pointer
        && !var.const_pointer
        && (var.name == "count"
            || var.name == format!("{}_count", ptr_name)
            || var.name == format!("{}_count", singular))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::ApiParser;

    fn parse(sources: &[(&str, &str)]) -> Vec<ApiDef> {
        sources
            .iter()
            .map(|(filename, src)| {
                let mut api_def = ApiDef::default();
                ApiParser::parse_string(src, filename, &mut api_def);
                api_def
            })
            .collect()
    }

    const DEMOZOO: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        extern opaque FlArena\n\
        #[view(crate::demoscene::query::SortOrder, fallback = TitleAz)]\n\
        enum DemozooSort { NameAsc, [from(TitleZa)] NameDesc }\n\
        struct DemozooExprNode { op: u32, value: u32, text: String }\n\
        struct DemozooTerm { id: u32, name: String }\n\
        struct DemozooTerms { terms: *const DemozooTerm, count: u32 }\n\
        struct DemozooProduction { title: String, found: bool }\n\
        struct DemozooFilter {\n\
            [from(entities)] entity_mask: u32,\n\
            platforms_any: *const u32,\n\
            platforms_any_count: u32,\n\
            [from(tree)] [with(crate::demozoo_abi::read_tree)] expr: *const DemozooExprNode,\n\
            expr_count: u32,\n\
        }\n\
        struct DemozooQuery { text: String, sort: DemozooSort, filter: DemozooFilter }\n\
        #[attributes(service)]\n\
        api Demozoo {\n\
            rp_demozoo_get_production(id: u32, arena: *FlArena) -> DemozooProduction\n\
            rp_demozoo_get_terms(kind: u32, arena: *FlArena) -> DemozooTerms\n\
            rp_demozoo_slot_update(slot: u32, query: *const DemozooQuery) -> u32\n\
        }";

    fn demozoo_model() -> PairedModel {
        resolve(&parse(&[("demozoo.def", DEMOZOO)])).expect("demozoo pairs")
    }

    /// A field naming an enum is not a key into structs, and indexing it as
    /// though it were is a panic.
    #[test]
    fn the_nesting_walk_steps_over_an_enum_typed_field() {
        let model = demozoo_model();
        let order = nesting_order(&model, ["DemozooQuery"].into_iter(), |_| true);

        assert_eq!(
            order,
            ["DemozooExprNode", "DemozooFilter", "DemozooQuery"],
            "each record after what it nests, and `sort` reaches no further"
        );
    }

    #[test]
    fn convention_pairs_types_and_infers_direction() {
        let model = demozoo_model();

        let production = &model.structs["DemozooProduction"];
        assert_eq!(production.view, "crate::demoscene::data::ProductionView");
        assert_eq!(
            production.dir,
            Direction {
                publish: true,
                read: false
            }
        );

        let query = &model.structs["DemozooQuery"];
        assert_eq!(query.view, "crate::demoscene::data::QueryView");
        assert!(query.dir.read && !query.dir.publish);
        assert!(model.structs["DemozooFilter"].dir.read);
        assert!(model.structs["DemozooExprNode"].dir.read);
        assert_eq!(
            query.fields[1].nested.as_deref(),
            Some("DemozooSort"),
            "a field naming a def type nests"
        );
    }

    #[test]
    fn found_field_marks_publish_from_option() {
        let production = &demozoo_model().structs["DemozooProduction"];
        assert!(production.found_synthesis);
        assert_eq!(
            production.fields.len(),
            1,
            "`found` is synthesized, not paired"
        );
    }

    #[test]
    fn renames_fuse_and_with_hatch_resolve() {
        let model = demozoo_model();
        let filter = &model.structs["DemozooFilter"];

        assert_eq!(filter.fields[0].host, "entities");
        assert_eq!(filter.fields[1].name, "platforms_any");
        assert_eq!(
            filter.fields[1].count.as_deref(),
            Some("platforms_any_count")
        );
        assert_eq!(filter.fields[2].host, "tree");
        assert_eq!(
            filter.fields[2].with.as_deref(),
            Some("crate::demozoo_abi::read_tree")
        );
        assert_eq!(filter.fields[2].count.as_deref(), Some("expr_count"));
        assert_eq!(
            filter.fields.len(),
            3,
            "count fields fuse into their pointer"
        );

        let terms = &model.structs["DemozooTerms"];
        assert_eq!(terms.fields[0].count.as_deref(), Some("count"));
        assert_eq!(terms.fields[0].nested.as_deref(), Some("DemozooTerm"));
    }

    #[test]
    fn a_singular_stem_count_fuses_with_its_list() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooPlacingEntry { position: u16 }\n\
            struct DemozooCompetition { placings: *const DemozooPlacingEntry, placing_count: u32 }\n\
            api Demozoo { rp_demozoo_get_competition(id: u32) -> DemozooCompetition }";
        let competition = &resolve(&parse(&[("demozoo.def", src)]))
            .expect("pairs")
            .structs["DemozooCompetition"];

        assert_eq!(competition.fields.len(), 1);
        assert_eq!(
            competition.fields[0].count.as_deref(),
            Some("placing_count")
        );
    }

    #[test]
    fn enum_hatch_carries_fallback_and_variant_renames() {
        let sort = &demozoo_model().enums["DemozooSort"];

        assert_eq!(sort.view, "crate::demoscene::query::SortOrder");
        assert_eq!(sort.fallback.as_deref(), Some("TitleAz"));
        assert_eq!(sort.variants[0].host, "NameAsc");
        assert_eq!(sort.variants[1].host, "TitleZa");
    }

    #[test]
    fn type_hatch_pairs_a_def_with_no_views_directive() {
        let src = "\
            #[module(catalog)]\n\
            #[view(crate::metacore::catalog::QueryView)]\n\
            struct CatalogQuery { text: String, offset: u32 }\n\
            #[attributes(service)]\n\
            api Catalog { rp_catalog_slot_update(query: *const CatalogQuery) -> u32 }";
        let model = resolve(&parse(&[("catalog.def", src)])).expect("hatch pairs");

        let query = &model.structs["CatalogQuery"];
        assert_eq!(query.view, "crate::metacore::catalog::QueryView");
        assert!(query.dir.read);
    }

    #[test]
    fn a_type_used_both_ways_carries_both_directions() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            api Demozoo {\n\
                rp_demozoo_get_term(id: u32) -> DemozooTerm\n\
                rp_demozoo_put_term(term: *const DemozooTerm) -> u32\n\
            }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("pairs");

        assert_eq!(
            model.structs["DemozooTerm"].dir,
            Direction {
                publish: true,
                read: true
            }
        );
    }

    #[test]
    fn a_fixed_field_must_cross_as_an_enum_and_takes_its_type_out_of_the_walk() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            enum DemozooState {\n\
                Idle = 0,\n\
                Ready = 1,\n\
            }\n\
            struct DemozooSlot { [fixed(Ready)] state: DemozooState, code: u16 }\n\
            api Demozoo { rp_demozoo_get_slot(id: u32) -> DemozooSlot }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("pairs");

        assert_eq!(
            model.structs["DemozooSlot"].fields[0].fixed.as_deref(),
            Some("Ready")
        );
        assert!(
            !model.enums.contains_key("DemozooState"),
            "a `[fixed]` field's type pairs with nothing"
        );

        let scalar = src.replace("state: DemozooState", "state: u32");
        let err = resolve(&parse(&[("demozoo.def", &scalar)])).unwrap_err();
        assert!(
            err.contains("`DemozooSlot.state` is `[fixed(...)]` but crosses as `u32`"),
            "{}",
            err
        );
    }

    #[test]
    fn a_pointer_without_a_count_partner_is_an_error() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            struct DemozooTerms { terms: *const DemozooTerm, kind: u32 }\n\
            api Demozoo { rp_demozoo_get_terms(kind: u32) -> DemozooTerms }";
        let err = resolve(&parse(&[("demozoo.def", src)])).unwrap_err();

        assert!(
            err.contains("`DemozooTerms.terms` is a pointer with no count partner"),
            "{}",
            err
        );
    }

    /// A hatched type pulls its nested types in, and they have only the
    /// convention to pair by.
    #[test]
    fn convention_pairing_without_a_views_directive_is_an_error() {
        let src = "\
            #[module(demozoo)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            #[view(crate::demoscene::data::TermsView)]\n\
            struct DemozooTerms { terms: *const DemozooTerm, count: u32 }\n\
            api Demozoo { rp_demozoo_get_terms(kind: u32) -> DemozooTerms }";
        let err = resolve(&parse(&[("demozoo.def", src)])).unwrap_err();

        assert!(err.contains("declares no `#[views("), "{}", err);
    }

    #[test]
    fn a_def_with_no_pairing_annotations_pairs_nothing() {
        let src = "\
            #[module(demozoo)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            api Demozoo { rp_demozoo_get_term(id: u32) -> DemozooTerm }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("nothing pairs");

        assert!(model.structs.is_empty() && model.enums.is_empty());
    }

    #[test]
    fn a_name_outside_the_def_prefix_cannot_pair_by_convention() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct SceneTerm { id: u32, name: String }\n\
            api Demozoo { rp_demozoo_get_term(id: u32) -> SceneTerm }";
        let err = resolve(&parse(&[("demozoo.def", src)])).unwrap_err();

        assert!(
            err.contains("does not start with the def prefix `Demozoo`"),
            "{}",
            err
        );
    }

    /// Resolution records the fallback rather than demanding it - the read emitter
    /// is what cannot proceed without one.
    #[test]
    fn an_enum_read_inbound_records_a_missing_fallback() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            enum DemozooSort { NameAsc, NameDesc }\n\
            struct DemozooQuery { sort: DemozooSort }\n\
            api Demozoo { rp_demozoo_slot_update(query: *const DemozooQuery) -> u32 }";
        let sort = &resolve(&parse(&[("demozoo.def", src)]))
            .expect("pairs")
            .enums["DemozooSort"];

        assert!(sort.dir.read && sort.fallback.is_none());
    }

    #[test]
    fn a_published_enum_needs_no_fallback() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            enum DemozooSort { NameAsc, NameDesc }\n\
            struct DemozooProduction { sort: DemozooSort }\n\
            api Demozoo { rp_demozoo_get_production(id: u32) -> DemozooProduction }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("pairs");

        assert_eq!(
            model.enums["DemozooSort"].view,
            "crate::demoscene::data::SortView"
        );
    }

    #[test]
    fn bitflags_and_handles_are_not_paired() {
        let src = "\
            #[module(demozoo)]\n\
            #[attributes(bitflags)]\n\
            enum DemozooCategory { Demo = 1, Intro = 2, }\n\
            #[handle(u32, invalid = 0xFFFFFFFF)]\n\
            struct DemozooSlot {}\n\
            api Demozoo { rp_demozoo_category(slot: DemozooSlot) -> DemozooCategory }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("nothing pairs");

        assert!(model.enums.is_empty() && model.structs.is_empty());
    }

    #[test]
    fn unreferenced_types_are_not_paired() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            api Demozoo { rp_demozoo_count() -> u32 }";
        let model = resolve(&parse(&[("demozoo.def", src)])).expect("nothing pairs");

        assert!(model.structs.is_empty());
    }

    /// Pairing follows a type across def files: the owning def's directive decides.
    #[test]
    fn pairing_crosses_def_files() {
        let catalog = "\
            #[module(catalog)]\n\
            #[views(crate::metacore::catalog)]\n\
            struct CatalogResult { status: u32 }";
        let demozoo = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            api Demozoo { rp_demozoo_slot_update(slot: u32) -> CatalogResult }";
        let model = resolve(&parse(&[
            ("catalog.def", catalog),
            ("demozoo.def", demozoo),
        ]))
        .expect("pairs");

        assert_eq!(
            model.structs["CatalogResult"].view,
            "crate::metacore::catalog::ResultView"
        );
    }

    /// A type whose own def opts out stays hand-written, even when a pairing def's
    /// slot names it.
    #[test]
    fn a_type_from_a_def_that_opts_out_does_not_pair() {
        let catalog = "\
            #[module(catalog)]\n\
            struct CatalogResult { status: u32 }";
        let demozoo = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            api Demozoo { rp_demozoo_slot_update(slot: u32) -> CatalogResult }";
        let model = resolve(&parse(&[
            ("catalog.def", catalog),
            ("demozoo.def", demozoo),
        ]))
        .expect("pairs");

        assert!(model.structs.is_empty());
    }

    #[test]
    fn a_renamed_found_field_pairs_like_any_other() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooParty { name: String, [from(exists)] found: bool }\n\
            api Demozoo { rp_demozoo_get_party(id: u32) -> DemozooParty }";
        let party = &resolve(&parse(&[("demozoo.def", src)]))
            .expect("pairs")
            .structs["DemozooParty"];

        assert!(!party.found_synthesis);
        assert_eq!(party.fields[1].name, "found");
        assert_eq!(party.fields[1].host, "exists");
    }

    #[test]
    fn a_fused_pair_resumes_at_the_field_after_the_count() {
        let src = "\
            #[module(catalog)]\n\
            #[views(crate::metacore::catalog)]\n\
            struct CatalogIds { ids: *const u32, count: u32, matched: u32 }\n\
            api Catalog { rp_catalog_get_ids(slot: u32) -> CatalogIds }";
        let ids = &resolve(&parse(&[("catalog.def", src)]))
            .expect("pairs")
            .structs["CatalogIds"];

        assert_eq!(ids.fields.len(), 2);
        assert_eq!(ids.fields[0].count.as_deref(), Some("count"));
        assert_eq!(ids.fields[1].name, "matched");
        assert_eq!(ids.fields[1].count, None);
    }

    #[test]
    fn a_pointer_in_last_position_is_an_error() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            struct DemozooTerms { count: u32, terms: *const DemozooTerm }\n\
            api Demozoo { rp_demozoo_get_terms(kind: u32) -> DemozooTerms }";
        let err = resolve(&parse(&[("demozoo.def", src)])).unwrap_err();

        assert!(
            err.contains("`DemozooTerms.terms` is a pointer with no count partner"),
            "{}",
            err
        );
    }

    /// A count is a u32 by value - a rightly-named field of any other shape is not one.
    #[test]
    fn a_count_partner_of_the_wrong_type_is_an_error() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            struct DemozooTerms { terms: *const DemozooTerm, count: u64 }\n\
            api Demozoo { rp_demozoo_get_terms(kind: u32) -> DemozooTerms }";
        let err = resolve(&parse(&[("demozoo.def", src)])).unwrap_err();
        assert!(
            err.contains("is a pointer with no count partner"),
            "{}",
            err
        );

        let src = src.replace("count: u64", "count: *const u32");
        let err = resolve(&parse(&[("demozoo.def", &src)])).unwrap_err();
        assert!(
            err.contains("is a pointer with no count partner"),
            "{}",
            err
        );
    }
}
