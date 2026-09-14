//! Round-trip tests, emitted from the paired model: per record that both
//! publishes and reads, a fixture view published into an arena and read back,
//! asserted field by field. Values are derived from the record itself.

use crate::emit_util::{
    group_imports, header, read_fn, type_name, write_call, write_use_list, WIDTH,
};
use crate::inbound_gen::{fallback, int_type, own_fields};
use crate::marshal_gen::{arena_use, miss_const, publish_fn, zero_of};
use crate::pairing::{
    nested_enum, nested_record, nesting_order, PairedEnum, PairedField, PairedModel, PairedStruct,
};
use crate::read_gen::reads_unsafely;
use heck::ToSnakeCase;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{BufWriter, Write};

/// Where the emitted tests reach for the two sides they drive.
pub struct TestPaths<'a> {
    /// Module path, from the host crate, of the consume-side reader modules:
    /// `<path>::<def>_read`.
    pub read_path: &'a str,
    /// Arena type the fixtures publish into: `<type>::new(bytes)` reserves one and
    /// as_raw() answers the raw pointer.
    pub arena: &'a str,
    /// Regeneration script named in the emitted header.
    pub script: &'a str,
}

/// Reserved per test: two elements per list and one short string per field, so any
/// def-declared record's fixture fits several times over.
const ARENA_BYTES: &str = "1 << 16";

/// Emit one module per def with round-trippable records, answering their module
/// names. A record round-trips when it is read back (`#[read]`) and the publish
/// side lowers it too.
pub fn generate(
    dir: &str,
    model: &PairedModel,
    publishable: &[String],
    paths: &TestPaths,
) -> std::io::Result<Vec<String>> {
    let mut per_def: BTreeMap<&str, Vec<&PairedStruct>> = BTreeMap::new();
    for paired in model.structs.values() {
        if paired.read_root && publishable.contains(&paired.name) {
            per_def.entry(&paired.def).or_default().push(paired);
        }
    }

    let mut modules = Vec::new();
    for (def, roots) in &per_def {
        let module = format!("{}_roundtrip", def);
        write_module(dir, &module, def, roots, model, paths)?;
        modules.push(module);
    }
    Ok(modules)
}

/// Every record a fixture is needed for. A `[read_with]` field is published like
/// any other, so what it nests is reached even though nothing asserts on it; a
/// `[with]` field is not lowered at all, so what it nests is never reached.
fn fixture_order(model: &PairedModel, roots: &[&PairedStruct], inbound: bool) -> Vec<String> {
    let roots = roots.iter().map(|r| r.name.as_str());
    nesting_order(model, roots, |field| !inbound || field.with.is_none())
}

fn write_module(
    dir: &str,
    module: &str,
    def: &str,
    roots: &[&PairedStruct],
    model: &PairedModel,
    paths: &TestPaths,
) -> std::io::Result<()> {
    let mut f = BufWriter::new(File::create(format!("{}/{}.rs", dir, module))?);
    let fixtures = fixture_order(model, roots, false);

    let arena = arena_use(model);
    let mut body = Vec::new();
    for name in &fixtures {
        write_fixture(&mut body, &model.structs[name], model, false)?;
    }
    for root in roots {
        write_test(&mut body, root, model, type_name(paths.arena), &arena)?;
    }
    let body = String::from_utf8(body).expect("the emitter writes UTF-8");
    // An import nothing names is a hard error in the consumer's lane.
    let cuts_arena = roots.iter().any(|r| arena[&r.name]);

    writeln!(f, "{}", header(paths.script))?;
    writeln!(
        f,
        "//! Round trips {}.def's records: a fixture view published into an arena",
        def
    )?;
    writeln!(
        f,
        "//! and read back, asserted field by field. A `[read_with]` field is the"
    )?;
    writeln!(f, "//! helper's, and is not asserted.")?;
    if body.contains("unsafe") {
        writeln!(f, "#![allow(unsafe_code)]")?;
    }
    writeln!(f)?;
    if cuts_arena {
        writeln!(f, "use {};", paths.arena)?;
        writeln!(f)?;
    }
    write_fn_imports(
        &mut f,
        &format!("{}::{}_read", paths.read_path, def),
        roots,
        read_fn,
    )?;
    writeln!(f)?;
    let marshal = format!("super::{}_marshal", def);
    write_fn_imports(&mut f, &marshal, roots, publish_fn)?;
    let optional: Vec<&PairedStruct> = roots
        .iter()
        .copied()
        .filter(|r| r.found_synthesis)
        .collect();
    if !optional.is_empty() {
        write_fn_imports(&mut f, &marshal, &optional, miss_const)?;
    }
    writeln!(f)?;
    let views = fixtures
        .iter()
        .map(|name| model.structs[name].view.as_str());
    for (module, types) in group_imports(views) {
        write_use_list(&mut f, module, &types)?;
    }
    writeln!(f)?;
    if cuts_arena {
        writeln!(f, "const ARENA_BYTES: u64 = {};", ARENA_BYTES)?;
    }
    write!(f, "{}", body)
}

/// `use <module>::{<name(root)>, ...};` for one of the two generated halves.
fn write_fn_imports(
    f: &mut impl Write,
    module: &str,
    roots: &[&PairedStruct],
    name: impl Fn(&str) -> String,
) -> std::io::Result<()> {
    let names: Vec<String> = roots.iter().map(|root| name(&root.name)).collect();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    write_use_list(f, module, &names)
}

/// What one field is populated with.
enum Fixture {
    /// An expression seeded by nth, so it varies from instance to instance.
    Seeded(String),
    /// One the emitter has no way to seed - an enum names a variant or nothing.
    Constant(String),
    /// A list's two elements, each seeded.
    List(Vec<String>),
}

/// `fn fixture_<record>(nth: u32) -> <View>` - every field a value of its own,
/// nth separating one instance of the record from the next.
fn write_fixture(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
    inbound: bool,
) -> std::io::Result<()> {
    let view = type_name(&paired.view);
    // A `[fixed]` field has no host counterpart to seed: the publish writes it.
    let fields: Vec<&PairedField> = paired
        .fields
        .iter()
        .filter(|field| field.fixed.is_none())
        .collect();
    let values: Vec<Fixture> = fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            // The hatch owns the crossing, so the test states nothing about the
            // field.
            if inbound && field.with.is_some() {
                return Fixture::Constant("Default::default()".to_owned());
            }
            fixture_value(model, paired, field, index + 1)
        })
        .collect();
    // An unused binding is a warning in the consumer's lane.
    let nth = if values.iter().any(|v| !matches!(v, Fixture::Constant(_))) {
        "nth"
    } else {
        "_nth"
    };

    writeln!(f)?;
    writeln!(
        f,
        "fn {}({}: u32) -> {} {{",
        fixture_fn(&paired.name),
        nth,
        view
    )?;
    writeln!(f, "    {} {{", view)?;
    for (field, value) in fields.iter().zip(&values) {
        match value {
            Fixture::Seeded(value) | Fixture::Constant(value) => {
                writeln!(f, "        {}: {},", field.host, value)?
            }
            Fixture::List(items) => write_call(
                f,
                "        ",
                &format!("{}: vec![", field.host),
                items,
                "],",
            )?,
        }
    }
    writeln!(f, "    }}")?;
    writeln!(f, "}}")
}

/// One field's fixture value: distinct from its neighbours' within the record, and
/// from the same field's in every other instance. An instance seeded nth seeds
/// what it nests `nth * 2` and `nth * 2 + 1`, so no two positions in the whole
/// tree share a seed.
fn fixture_value(
    model: &PairedModel,
    paired: &PairedStruct,
    field: &PairedField,
    ord: usize,
) -> Fixture {
    if field.count.is_some() {
        return match nested_record(model, field) {
            Some(ty) => Fixture::List(vec![
                format!("{}(nth * 2)", fixture_fn(ty)),
                format!("{}(nth * 2 + 1)", fixture_fn(ty)),
            ]),
            None => Fixture::List(vec![
                scalar_value(&field.ty, ord, 0),
                scalar_value(&field.ty, ord, 1),
            ]),
        };
    }
    if let Some(ty) = nested_record(model, field) {
        let value = format!("{}(nth * 2)", fixture_fn(ty));
        return Fixture::Seeded(if model.structs[ty].found_synthesis {
            format!("Some({})", value)
        } else {
            value
        });
    }
    if let Some(paired) = field.nested.as_deref().and_then(|ty| model.enums.get(ty)) {
        // The second variant: a zeroed record already reads as the first, so that
        // one would not tell a published value from an unpublished one.
        let variant = paired
            .variants
            .get(1)
            .or_else(|| paired.variants.first())
            .unwrap_or_else(|| panic!("api_gen: `{}` declares no variants", paired.name));
        return Fixture::Constant(format!("{}::{}", paired.view, variant.host));
    }
    // Qualified by the record, so copying a same-named field from one record into
    // another is a value that names where it came from.
    if field.ty == "String" {
        return Fixture::Seeded(format!(
            "format!(\"{}.{}{{}}\", nth)",
            paired.name.to_snake_case(),
            field.name
        ));
    }
    Fixture::Seeded(scalar_value(&field.ty, ord, 0))
}

/// A scalar's fixture value: its ordinal, offset by the instance seed and by where
/// it sits in a list. A bool carries one bit, so it can only alternate - two
/// bool fields an even number apart necessarily share a value.
fn scalar_value(ty: &str, ord: usize, offset: usize) -> String {
    match ty {
        // A bool reads only the parity of its seed, so it takes the undoubled
        // one: doubling would fix its value by ordinal alone, and two elements of
        // the same list would stop being told apart by their flags. Spelled
        // is_multiple_of because % 2 == 0 is denied in the consumer's lane.
        "bool" => format!("({} + nth).is_multiple_of(2)", ord + offset),
        // nth is already a u32, and a cast to the type a value already has is
        // one the consumer's lint set refuses.
        "u32" => format!("{} + nth * 2", ord + offset),
        _ => format!("({} + nth * 2) as {}", ord + offset, ty),
    }
}

fn write_test(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
    arena_ty: &str,
    arena: &BTreeMap<String, bool>,
) -> std::io::Result<()> {
    let path = paired.name.to_snake_case();
    let unsafely = reads_unsafely(model, &paired.name);

    writeln!(f)?;
    writeln!(f, "#[test]")?;
    writeln!(f, "fn a_published_{}_reads_back() {{", path)?;
    writeln!(f, "    let view = {}(0);", fixture_fn(&paired.name))?;
    if arena[&paired.name] {
        writeln!(f, "    let arena = {}::new(ARENA_BYTES);", arena_ty)?;
        writeln!(
            f,
            "    // SAFETY: arena is live for the call and outlives every read below."
        )?;
        writeln!(
            f,
            "    let raw = unsafe {{ {}(&view, arena.as_raw().cast()) }};",
            publish_fn(&paired.name)
        )?;
    } else {
        writeln!(f, "    let raw = {}(&view);", publish_fn(&paired.name))?;
    }
    let read = format!("{}(&raw)", read_fn(&paired.name));
    if unsafely {
        writeln!(
            f,
            "    // SAFETY: everything raw addresses was just cut from arena."
        )?;
        writeln!(f, "    let read = unsafe {{ {} }};", read)?;
    } else {
        writeln!(f, "    let read = {};", read)?;
    }
    if paired.found_synthesis {
        writeln!(f, "    let Some(read) = read else {{")?;
        writeln!(
            f,
            "        panic!(\"{}.found: a populated fixture publishes found\");",
            path
        )?;
        writeln!(f, "    }};")?;
    }

    let site = Site {
        read: "read".to_owned(),
        view: "view".to_owned(),
        path,
        args: Vec::new(),
        depth: 0,
        inbound: false,
    };
    write_asserts(f, model, paired, &site)?;

    // The other half of the Option, which no populated fixture reaches.
    if paired.found_synthesis {
        let read = format!("{}(&{})", read_fn(&paired.name), miss_const(&paired.name));
        writeln!(f)?;
        if unsafely {
            writeln!(
                f,
                "    // SAFETY: the miss constant addresses nothing at all."
            )?;
            writeln!(f, "    let miss = unsafe {{ {} }};", read)?;
        } else {
            writeln!(f, "    let miss = {};", read)?;
        }
        write_call(
            f,
            "    ",
            "assert!(",
            &[
                "miss.is_none()".to_owned(),
                format!(
                    "\"{}.found: the miss constant reads back as None\"",
                    site.path
                ),
            ],
            ");",
        )?;
    }
    writeln!(f, "}}")
}

/// Where one level of the assert walk sits: the two expressions being compared,
/// the field path they carry, and the loop indices that path interpolates.
struct Site {
    read: String,
    view: String,
    path: String,
    args: Vec<String>,
    depth: usize,
    /// Inbound, where both sides are the host view and the hatch is `[with]`.
    inbound: bool,
}

/// One assert per field of paired, site.read against site.view, each
/// carrying the path down to the field it checks.
fn write_asserts(
    f: &mut impl Write,
    model: &PairedModel,
    paired: &PairedStruct,
    site: &Site,
) -> std::io::Result<()> {
    let indent = " ".repeat(4 + site.depth * 4);
    let hatched = |f: &&PairedField| {
        if f.fixed.is_some() {
            return false;
        }
        if site.inbound {
            f.with.is_none()
        } else {
            f.read_with.is_none()
        }
    };
    for field in paired.fields.iter().filter(hatched) {
        let named = if site.inbound {
            &field.host
        } else {
            &field.name
        };
        let read = format!("{}.{}", site.read, named);
        let view = format!("{}.{}", site.view, field.host);
        let path = format!("{}.{}", site.path, field.name);

        match (&field.count, nested_record(model, field)) {
            // A list of records: the count first, then the elements pairwise.
            (Some(count), Some(ty)) => {
                write_assert(
                    f,
                    &indent,
                    &format!("{}.len()", read),
                    &format!("{}.len()", view),
                    &format!("{}.{}", site.path, count),
                    &site.args,
                )?;
                let index = format!("index_{}", site.depth);
                let mut args = site.args.clone();
                args.push(index.clone());
                let inner = Site {
                    read: format!("read_{}", site.depth + 1),
                    view: format!("view_{}", site.depth + 1),
                    path: format!("{}[{{}}]", path),
                    args,
                    depth: site.depth + 1,
                    inbound: site.inbound,
                };

                let bindings = format!("({}, ({}, {}))", index, inner.read, inner.view);
                let items = format!("{}.iter().zip(&{}).enumerate()", read, view);
                let one_line = format!("{}for {} in {} {{", indent, bindings, items);
                if one_line.len() <= WIDTH {
                    writeln!(f, "{}", one_line)?;
                } else {
                    writeln!(f, "{}for {} in", indent, bindings)?;
                    writeln!(f, "{}    {}", indent, items)?;
                    writeln!(f, "{}{{", indent)?;
                }
                write_asserts(f, model, &model.structs[ty], &inner)?;
                writeln!(f, "{}}}", indent)?;
            }
            // A list of scalars is copied out whole, so it compares whole.
            (Some(_), None) => write_assert(f, &indent, &read, &view, &path, &site.args)?,
            (None, Some(ty)) => {
                let (read, view) = if model.structs[ty].found_synthesis {
                    // Both sides hold an Option; the fixture populates it, so
                    // the absent arm is the record failing to cross at all.
                    let (bound_read, bound_view) = (
                        format!("{}_{}", site.read, field.name),
                        format!("{}_{}", site.view, field.name),
                    );
                    writeln!(
                        f,
                        "{}let (Some({}), Some({})) = (&{}, &{}) else {{",
                        indent, bound_read, bound_view, read, view
                    )?;
                    writeln!(
                        f,
                        "{}    panic!(\"{}: a populated fixture publishes it\"{});",
                        indent,
                        path,
                        site.args
                            .iter()
                            .map(|arg| format!(", {}", arg))
                            .collect::<String>()
                    )?;
                    writeln!(f, "{}}};", indent)?;
                    (bound_read, bound_view)
                } else {
                    (read, view)
                };
                let inner = Site {
                    read,
                    view,
                    path,
                    args: site.args.clone(),
                    depth: site.depth,
                    inbound: site.inbound,
                };
                write_asserts(f, model, &model.structs[ty], &inner)?;
            }
            (None, None) => write_assert(f, &indent, &read, &view, &path, &site.args)?,
        }
    }
    Ok(())
}

/// `assert_eq!(<read>, <view>, "<path>", <args>);` - the path, and the loop indices
/// it interpolates, are what the failure names.
fn write_assert(
    f: &mut impl Write,
    indent: &str,
    read: &str,
    view: &str,
    path: &str,
    args: &[String],
) -> std::io::Result<()> {
    let mut all = vec![read.to_owned(), view.to_owned(), format!("\"{}\"", path)];
    all.extend(args.iter().cloned());
    write_call(f, indent, "assert_eq!(", &all, ");")
}

fn fixture_fn(name: &str) -> String {
    format!("fixture_{}", name.to_snake_case())
}

///////////////////////////////////////////////////////////////////////////////
// Inbound.

/// Where the emitted inbound tests reach for the raw side they lower onto.
pub struct InboundTestPaths<'a> {
    /// Crate holding the raw ABI modules: `<crate>::<def>` is aliased to abi.
    pub abi_crate: &'a str,
    /// Verbatim use paths the lowering may need; only the ones it names are
    /// emitted, since an unused import is a warning in the consumer's lane.
    pub uses: &'a [String],
    /// Regeneration script named in the emitted header.
    pub script: &'a str,
}

/// Emit one module per def with round-trippable inbound records: a fixture view
/// lowered onto the ABI and read back through the generated reader, asserted
/// field by field.
pub fn generate_inbound(
    dir: &str,
    model: &PairedModel,
    inbound: &[String],
    paths: &InboundTestPaths,
) -> std::io::Result<Vec<String>> {
    let mut per_def: BTreeMap<&str, Vec<&PairedStruct>> = BTreeMap::new();
    for name in inbound_roots(model, inbound) {
        let paired = &model.structs[name];
        per_def.entry(&paired.def).or_default().push(paired);
    }

    let mut modules = Vec::new();
    for (def, roots) in &per_def {
        let module = format!("{}_inbound_roundtrip", def);
        write_inbound_module(dir, &module, def, roots, model, paths)?;
        modules.push(module);
    }
    Ok(modules)
}

/// The inbound records a test drives: the ones no other inbound record nests,
/// minus the ones a fixture cannot be lowered onto the ABI.
fn inbound_roots<'a>(model: &PairedModel, inbound: &'a [String]) -> Vec<&'a str> {
    let mut nested = BTreeSet::new();
    for name in inbound {
        for field in own_fields(&model.structs[name]) {
            if let Some(ty) = nested_record(model, field) {
                nested.insert(ty);
            }
        }
    }

    let (roots, skipped): (Vec<&str>, Vec<&str>) = inbound
        .iter()
        .map(String::as_str)
        .filter(|name| !nested.contains(name))
        .partition(|name| lowers_whole(model, name));
    if !skipped.is_empty() {
        println!(
            "api_gen: inbound: {} record(s) with no generated round trip: {}",
            skipped.len(),
            skipped.join(", ")
        );
    }
    roots
}

/// Whether a fixture of name lowers onto the ABI. A list of records is the one
/// shape that does not: its elements would have to be lowered into storage the
/// lowering answers a pointer into, and it has none to give.
fn lowers_whole(model: &PairedModel, name: &str) -> bool {
    own_fields(&model.structs[name]).all(|field| match nested_record(model, field) {
        Some(ty) => field.count.is_none() && lowers_whole(model, ty),
        None => true,
    })
}

fn write_inbound_module(
    dir: &str,
    module: &str,
    def: &str,
    roots: &[&PairedStruct],
    model: &PairedModel,
    paths: &InboundTestPaths,
) -> std::io::Result<()> {
    let records = fixture_order(model, roots, true);
    let mut body = Vec::new();
    for name in &records {
        write_fixture(&mut body, &model.structs[name], model, true)?;
        write_lowering(&mut body, &model.structs[name], model)?;
    }
    for root in roots {
        write_inbound_test(&mut body, root, model)?;
        for site in enum_sites(model, root) {
            write_fallback_test(&mut body, root, &site)?;
        }
    }
    let body = String::from_utf8(body).expect("emitted utf8");

    let mut f = BufWriter::new(File::create(format!("{}/{}.rs", dir, module))?);
    writeln!(f, "{}", header(paths.script))?;
    writeln!(
        f,
        "//! Round trips {}.def's inbound records: a fixture view lowered onto the",
        def
    )?;
    writeln!(
        f,
        "//! ABI and read back, asserted field by field. A `[with]` field is the"
    )?;
    writeln!(f, "//! helper's: it lowers as a zero and is not asserted.")?;
    // A host enum may carry variants the def never declares, and then may not.
    writeln!(f, "#![allow(unreachable_patterns)]")?;
    writeln!(f, "#![allow(unsafe_code)]")?;
    writeln!(f)?;
    writeln!(f, "use core::ptr;")?;
    for path in paths.uses.iter().filter(|p| body.contains(type_name(p))) {
        writeln!(f, "use {};", path)?;
    }
    writeln!(f)?;
    writeln!(f, "use {}::{} as abi;", paths.abi_crate, def)?;
    writeln!(f)?;
    write_fn_imports(&mut f, &format!("super::{}_inbound", def), roots, read_fn)?;
    writeln!(f)?;
    let views = records
        .iter()
        .map(|name| model.structs[name].view.as_str())
        .chain(
            records
                .iter()
                .flat_map(|name| own_fields(&model.structs[name]))
                .filter_map(|field| nested_enum(model, field))
                .map(|paired| paired.view.as_str()),
        );
    for (module, types) in group_imports(views) {
        write_use_list(&mut f, module, &types)?;
    }
    write!(f, "{}", body)
}

/// `fn lower_<record>(view: &<View>) -> abi::<Record>` - the arm the inbound test
/// crosses on, borrowing every string and list from view.
fn write_lowering(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
) -> std::io::Result<()> {
    let view = type_name(&paired.view);
    writeln!(f)?;
    writeln!(
        f,
        "fn {}(view: &{}) -> abi::{} {{",
        lower_fn(&paired.name),
        view,
        paired.name
    )?;
    writeln!(f, "    abi::{} {{", paired.name)?;
    for field in &paired.fields {
        write_lowered_field(f, field, model)?;
    }
    writeln!(f, "    }}")?;
    writeln!(f, "}}")
}

fn write_lowered_field(
    f: &mut impl Write,
    field: &PairedField,
    model: &PairedModel,
) -> std::io::Result<()> {
    let indent = "        ";
    if let Some(count) = &field.count {
        let (items, len) = if field.with.is_some() {
            ("ptr::null()".to_owned(), "0".to_owned())
        } else {
            (
                format!("view.{}.as_ptr()", field.host),
                format!("view.{}.len() as u32", field.host),
            )
        };
        writeln!(f, "{}{}: {},", indent, field.name, items)?;
        return writeln!(f, "{}{}: {},", indent, count, len);
    }
    if field.with.is_some() {
        let zero = zero_lowering(field, model);
        return writeln!(f, "{}{}: {},", indent, field.name, zero);
    }
    if field.ty == "String" {
        return writeln!(
            f,
            "{}{}: RawStr::borrow(&view.{}),",
            indent, field.name, field.host
        );
    }
    if let Some(ty) = nested_record(model, field) {
        return writeln!(
            f,
            "{}{}: {}(&view.{}),",
            indent,
            field.name,
            lower_fn(ty),
            field.host
        );
    }
    if let Some(paired) = nested_enum(model, field) {
        let host = type_name(&paired.view);
        writeln!(f, "{}{}: match view.{} {{", indent, field.name, field.host)?;
        for variant in &paired.variants {
            writeln!(
                f,
                "{}    {}::{} => abi::{}::{},",
                indent, host, variant.host, paired.name, variant.name
            )?;
        }
        writeln!(
            f,
            "{}    _ => abi::{}::{},",
            indent,
            paired.name,
            undeclared_arm(paired)
        )?;
        return writeln!(f, "{}}},", indent);
    }
    writeln!(f, "{}{}: view.{},", indent, field.name, field.host)
}

/// What a `[with]` field lowers as: the hatch owns the crossing, so the test
/// hands its helper the empty value and asserts nothing about what came back.
fn zero_lowering(field: &PairedField, model: &PairedModel) -> String {
    if field.ty == "String" {
        return "RawStr::EMPTY".to_owned();
    }
    if let Some(paired) = nested_enum(model, field) {
        return format!("abi::{}::{}", paired.name, undeclared_arm(paired));
    }
    zero_of(&field.ty).unwrap_or_else(|| {
        panic!(
            "api_gen: `{}` is a `[with]` field crossing as `{}`, which has no known zero",
            field.name, field.ty
        )
    })
}

/// The ABI variant a host variant the def never declared lowers as: the
/// fallback's own ABI variant, or the zero variant when the fallback is host-only.
fn undeclared_arm(paired: &PairedEnum) -> &str {
    let named = |name: Option<&str>| {
        paired
            .variants
            .iter()
            .find(|variant| Some(variant.host.as_str()) == name)
    };
    named(paired.fallback.as_deref())
        .or_else(|| named(paired.zero.as_deref()))
        .or_else(|| paired.variants.first())
        .map(|variant| variant.name.as_str())
        .unwrap_or_else(|| panic!("api_gen: `{}` declares no variants", paired.name))
}

fn write_inbound_test(
    f: &mut impl Write,
    paired: &PairedStruct,
    model: &PairedModel,
) -> std::io::Result<()> {
    let path = paired.name.to_snake_case();
    writeln!(f)?;
    writeln!(f, "#[test]")?;
    writeln!(f, "fn an_inbound_{}_reads_back() {{", path)?;
    writeln!(f, "    let view = {}(0);", fixture_fn(&paired.name))?;
    writeln!(f, "    let raw = {}(&view);", lower_fn(&paired.name))?;
    write_inbound_read(f, paired)?;

    let site = Site {
        read: "read".to_owned(),
        view: "view".to_owned(),
        path,
        args: Vec::new(),
        depth: 0,
        inbound: true,
    };
    write_asserts(f, model, paired, &site)?;
    writeln!(f, "}}")
}

/// The read both inbound tests share: the reader over the lowered record, which
/// borrows from the fixture the caller still holds.
fn write_inbound_read(f: &mut impl Write, paired: &PairedStruct) -> std::io::Result<()> {
    writeln!(
        f,
        "    // SAFETY: raw addresses view, which outlives the read."
    )?;
    writeln!(
        f,
        "    let read = unsafe {{ {}(ptr::addr_of!(raw)) }};",
        read_fn(&paired.name)
    )
}

/// One enum a reader decodes, and where it sits under the record a test drives.
struct EnumSite {
    /// Field path from the raw record, in def names.
    raw: String,
    /// The same path from the view the reader answered, in host names.
    read: String,
    /// The path a failure names, and what the test is named after.
    label: String,
    host: String,
    fallback: String,
    int: &'static str,
}

/// Every enum a fixture of paired crosses, each reachable by value: a list
/// element is not, and neither is a `[with]` field's.
fn enum_sites(model: &PairedModel, paired: &PairedStruct) -> Vec<EnumSite> {
    fn walk(
        model: &PairedModel,
        name: &str,
        prefix: &str,
        read_prefix: &str,
        label: &str,
        out: &mut Vec<EnumSite>,
    ) {
        for field in own_fields(&model.structs[name]).filter(|f| f.count.is_none()) {
            if let Some(paired) = nested_enum(model, field) {
                out.push(EnumSite {
                    raw: format!("{}.{}", prefix, field.name),
                    read: format!("{}.{}", read_prefix, field.host),
                    label: format!("{}.{}", label, field.name),
                    host: type_name(&paired.view).to_owned(),
                    fallback: fallback(paired).to_owned(),
                    int: int_type(paired),
                });
            } else if let Some(ty) = nested_record(model, field) {
                walk(
                    model,
                    ty,
                    &format!("{}.{}", prefix, field.name),
                    &format!("{}.{}", read_prefix, field.host),
                    &format!("{}.{}", label, field.name),
                    out,
                );
            }
        }
    }

    let mut sites = Vec::new();
    walk(
        model,
        &paired.name,
        "raw",
        "read",
        &paired.name.to_snake_case(),
        &mut sites,
    );
    sites
}

/// A discriminant the def never declared, written as the integer it crosses as.
fn write_fallback_test(
    f: &mut impl Write,
    paired: &PairedStruct,
    site: &EnumSite,
) -> std::io::Result<()> {
    writeln!(f)?;
    writeln!(f, "#[test]")?;
    writeln!(
        f,
        "fn an_undeclared_{}_reads_the_fallback() {{",
        site.label.replace('.', "_")
    )?;
    writeln!(f, "    let view = {}(0);", fixture_fn(&paired.name))?;
    writeln!(f, "    let mut raw = {}(&view);", lower_fn(&paired.name))?;
    writeln!(
        f,
        "    // SAFETY: written as the integer the enum crosses as, which is also the only way"
    )?;
    writeln!(f, "    // the reader ever looks at it.")?;
    write_call(
        f,
        "    ",
        "unsafe { ptr::write(",
        &[
            format!("ptr::addr_of_mut!({}).cast::<{}>()", site.raw, site.int),
            format!("{}::MAX", site.int),
        ],
        ") };",
    )?;
    write_inbound_read(f, paired)?;
    write_call(
        f,
        "    ",
        "assert_eq!(",
        &[
            site.read.clone(),
            format!("{}::{}", site.host, site.fallback),
            format!("\"{}\"", site.label),
        ],
        ");",
    )?;
    writeln!(f, "}}")
}

fn lower_fn(name: &str) -> String {
    format!("lower_{}", name.to_snake_case())
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
            start_year: u16,\n\
            [read_with(crate::services::demozoo::entity_id)] series_id: u32,\n\
            competitions: *const DemozooCompetition,\n\
            competition_count: u32,\n\
            soundtracks: *const u32,\n\
            soundtrack_count: u32,\n\
            found: bool,\n\
        }\n\
        #[read]\n\
        struct DemozooHeat { best: DemozooPlacingEntry }\n\
        enum DemozooState {\n\
            Idle = 0,\n\
            Ready = 1,\n\
        }\n\
        #[read]\n\
        struct DemozooSlot { [fixed(Ready)] state: DemozooState, code: u16 }\n\
        struct DemozooPlacing { position: u16, found: bool }\n\
        #[read]\n\
        struct DemozooEntry { title: String, placing: DemozooPlacing }\n\
        struct DemozooLap { best: DemozooPlacing }\n\
        #[read]\n\
        struct DemozooRace { title: String, laps: *const DemozooLap, lap_count: u32 }\n\
        #[read]\n\
        struct DemozooReleaser {\n\
            [with(crate::demozoo_abi::publish_name)] name: String,\n\
        }\n\
        api Demozoo {\n\
            rp_demozoo_get_party_detail(id: u32, arena: *FlArena) -> DemozooPartyDetail\n\
            rp_demozoo_get_heat(id: u32, arena: *FlArena) -> DemozooHeat\n\
            rp_demozoo_get_slot(id: u32, arena: *FlArena) -> DemozooSlot\n\
            rp_demozoo_get_entry(id: u32, arena: *FlArena) -> DemozooEntry\n\
            rp_demozoo_get_race(id: u32, arena: *FlArena) -> DemozooRace\n\
            rp_demozoo_get_releaser(id: u32, arena: *FlArena) -> DemozooReleaser\n\
        }";

    fn model(src: &str) -> (Vec<crate::api_parser::ApiDef>, PairedModel) {
        model_named(src, "demozoo.def")
    }

    fn model_named(src: &str, file: &str) -> (Vec<crate::api_parser::ApiDef>, PairedModel) {
        let mut api_def = crate::api_parser::ApiDef::default();
        ApiParser::parse_string(src, file, &mut api_def);
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);
        let paired = crate::pairing::resolve(&api_defs).expect("pairs");
        (api_defs, paired)
    }

    /// None when nothing round-trips.
    fn emit_src(tag: &str, src: &str) -> Option<String> {
        let dir = std::env::temp_dir().join(format!("api_gen_test_{}_{}", std::process::id(), tag));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let (api_defs, paired) = model(src);

        let modules = generate(
            dir.to_str().unwrap(),
            &paired,
            &crate::marshal_gen::publishable(&api_defs, &paired),
            &TestPaths {
                read_path: "replay_plugin::generated",
                arena: "flowi::Arena",
                script: "scripts/gen.sh",
            },
        )
        .expect("generate");

        let emitted = modules.first().map(|module| {
            std::fs::read_to_string(dir.join(format!("{}.rs", module))).expect("read")
        });
        let _ = std::fs::remove_dir_all(&dir);
        emitted
    }

    fn emit(tag: &str) -> String {
        emit_src(tag, DEMOZOO).expect("demozoo round-trips")
    }

    #[test]
    fn a_root_that_publishes_and_reads_gets_a_test() {
        let emitted = emit("root");

        assert!(emitted.contains("fn a_published_demozoo_party_detail_reads_back() {"));
        assert!(emitted.contains(
            "    let raw = unsafe { publish_demozoo_party_detail(&view, arena.as_raw().cast()) };\n\
             \x20   // SAFETY: everything raw addresses was just cut from arena.\n\
             \x20   let read = unsafe { read_demozoo_party_detail(&raw) };"
        ));
    }

    #[test]
    fn a_root_the_publish_side_still_hand_writes_gets_no_test() {
        assert!(!emit("hand_published").contains("demozoo_releaser"));
    }

    #[test]
    fn a_root_that_copies_nothing_round_trips_without_an_arena() {
        let emitted = emit("arena_free_root");

        assert!(emitted.contains(
            "    let view = fixture_demozoo_slot(0);\n\
             \x20   let raw = publish_demozoo_slot(&view);\n"
        ));
        assert!(!emitted.contains("unsafe { publish_demozoo_slot("));
    }

    /// The arena import, its byte count and the unsafe allow are all things a def
    /// of only scalars would otherwise carry without ever naming.
    #[test]
    fn a_def_that_cuts_nothing_imports_no_arena() {
        let scalars = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            extern opaque FlArena\n\
            #[read]\n\
            struct DemozooStamp { code: u16 }\n\
            api Demozoo { rp_demozoo_get_stamp(id: u32, arena: *FlArena) -> DemozooStamp }";
        let emitted = emit_src("no_arena_import", scalars).expect("stamp round-trips");

        assert!(emitted.contains("let raw = publish_demozoo_stamp(&view);"));
        assert!(!emitted.contains("use flowi::Arena;"));
        assert!(!emitted.contains("ARENA_BYTES"));
        assert!(!emitted.contains("unsafe"));
    }

    #[test]
    fn fixtures_are_derived_and_distinct_per_field() {
        let emitted = emit("fixtures");

        assert!(emitted.contains(
            "fn fixture_demozoo_placing_entry(nth: u32) -> PlacingEntryView {\n\
             \x20   PlacingEntryView {\n\
             \x20       production_id: 1 + nth * 2,\n\
             \x20       position: (2 + nth * 2) as u16,\n\
             \x20   }\n\
             }"
        ));
        assert!(emitted.contains("name: format!(\"demozoo_competition.name{}\", nth),"));
        // Over the width, so it also pins how a list breaks across lines.
        assert!(emitted.contains(
            "        placings: vec![\n\
             \x20           fixture_demozoo_placing_entry(nth * 2),\n\
             \x20           fixture_demozoo_placing_entry(nth * 2 + 1),\n\
             \x20       ],"
        ));
        assert!(emitted.contains("soundtracks: vec![5 + nth * 2, 6 + nth * 2],"));
    }

    #[test]
    fn asserts_carry_the_field_path() {
        let emitted = emit("paths");

        assert!(emitted.contains(
            "assert_eq!(read.start_year, view.start_year, \"demozoo_party_detail.start_year\");"
        ));
        assert!(emitted.contains(
            "            assert_eq!(\n\
             \x20               read_2.position,\n\
             \x20               view_2.position,\n\
             \x20               \"demozoo_party_detail.competitions[{}].placings[{}].position\",\n\
             \x20               index_0,\n\
             \x20               index_1,\n\
             \x20           );"
        ));
    }

    #[test]
    fn a_list_compares_its_count_and_then_its_elements() {
        let emitted = emit("lists");

        assert!(emitted.contains("\"demozoo_party_detail.competition_count\""));
        assert!(emitted.contains(
            "    for (index_0, (read_1, view_1)) in\n\
             \x20       read.competitions.iter().zip(&view.competitions).enumerate()\n\
             \x20   {"
        ));
        assert!(emitted.contains(
            "assert_eq!(read.soundtracks, view.soundtracks, \"demozoo_party_detail.soundtracks\");"
        ));
    }

    /// The fixture populates it because the publish side still copies it.
    #[test]
    fn a_read_with_field_is_populated_but_not_asserted() {
        let emitted = emit("hatch");

        assert!(emitted.contains("series_id: 3 + nth * 2,"));
        assert!(!emitted.contains("series_id, view.series_id"));
    }

    #[test]
    fn found_synthesis_is_asserted_by_the_read_answering_some() {
        assert!(emit("found").contains(
            "    let Some(read) = read else {\n\
             \x20       panic!(\"demozoo_party_detail.found: a populated fixture publishes found\");\n\
             \x20   };"
        ));
    }

    #[test]
    fn a_record_nested_by_value_flattens_into_its_holder() {
        let emitted = emit("by_value");

        assert!(emitted.contains("        best: fixture_demozoo_placing_entry(nth * 2),"));
        assert!(emitted.contains("    let read = read_demozoo_heat(&raw);"));
        assert!(emitted.contains(
            "assert_eq!(read.best.position, view.best.position, \"demozoo_heat.best.position\");"
        ));
    }

    #[test]
    fn an_optional_record_nested_by_value_is_unwrapped_before_its_fields() {
        let emitted = emit("nested_option");

        assert!(emitted.contains("        placing: Some(fixture_demozoo_placing(nth * 2)),"));
        assert!(emitted.contains(
            "    let (Some(read_placing), Some(view_placing)) = (&read.placing, &view.placing) \
             else {\n\
             \x20       panic!(\"demozoo_entry.placing: a populated fixture publishes it\");\n\
             \x20   };"
        ));
        assert!(emitted.contains(
            "assert_eq!(read_placing.position, view_placing.position, \
             \"demozoo_entry.placing.position\");"
        ));
    }

    #[test]
    fn an_optional_record_inside_a_list_element_unwraps_under_the_loop() {
        let emitted = emit("nested_option_in_list");

        assert!(emitted.contains(
            "        let (Some(read_1_best), Some(view_1_best)) = (&read_1.best, &view_1.best) \
             else {\n\
             \x20           panic!(\"demozoo_race.laps[{}].best: a populated fixture publishes \
             it\", index_0);\n\
             \x20       };"
        ));
    }

    #[test]
    fn bool_fields_alternate_by_field_and_by_instance() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            #[read]\n\
            struct DemozooFlags { rated: bool, pinned: bool, hidden: bool }\n\
            api Demozoo { rp_demozoo_get_flags(id: u32) -> DemozooFlags }";
        let emitted = emit_src("bools", src).expect("flags round-trip");

        // The seed is undoubled where every other scalar's is doubled: a doubled
        // one has a parity fixed by the ordinal, so every instance would agree.
        assert!(emitted.contains(
            "        rated: (1 + nth).is_multiple_of(2),\n\
             \x20       pinned: (2 + nth).is_multiple_of(2),\n\
             \x20       hidden: (3 + nth).is_multiple_of(2),"
        ));
    }

    #[test]
    fn a_def_with_no_round_trippable_record_emits_nothing() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            struct DemozooTerm { id: u32, name: String }\n\
            api Demozoo { rp_demozoo_get_term(id: u32) -> DemozooTerm }";

        assert!(emit_src("empty", src).is_none());
    }

    const INBOUND: &str = "\
        #[module(demozoo)]\n\
        #[views(crate::demoscene::data)]\n\
        extern opaque FlArena\n\
        #[view(crate::demoscene::query::SortOrder, fallback = Relevance)]\n\
        enum DemozooSort {\n\
            Relevance = 0,\n\
            [from(TitleAz)] NameAsc = 1,\n\
        }\n\
        struct DemozooExprNode { op: u32, value: u32 }\n\
        struct DemozooFilter {\n\
            country: String,\n\
            platforms_any: *const u32,\n\
            platforms_any_count: u32,\n\
            [from(tree)] [with(crate::demozoo_abi::read_tree)] expr: *const DemozooExprNode,\n\
            expr_count: u32,\n\
        }\n\
        struct DemozooQuery {\n\
            text: String,\n\
            [from(categories)] category_mask: u32,\n\
            sort: DemozooSort,\n\
            [with(crate::seams::entities)] entity_mask: u32,\n\
            [with(crate::seams::locale)] country: String,\n\
            [with(crate::demozoo_abi::order_from_raw)] order: DemozooSort,\n\
            filter: DemozooFilter,\n\
        }\n\
        api Demozoo {\n\
            rp_demozoo_slot_update(slot: u32, query: *const DemozooQuery) -> u32\n\
        }";

    fn emit_inbound(tag: &str, src: &str) -> String {
        let dir = std::env::temp_dir().join(format!(
            "api_gen_inbound_test_{}_{}",
            std::process::id(),
            tag
        ));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let (api_defs, paired) = model(src);

        let modules = generate_inbound(
            dir.to_str().unwrap(),
            &paired,
            &crate::inbound_gen::inbound(&api_defs, &paired),
            &InboundTestPaths {
                abi_crate: "replay_plugin",
                uses: &["flowi::RawStr".to_owned()],
                script: "scripts/gen.sh",
            },
        )
        .expect("generate");
        let module = modules.first().expect("one module").clone();
        std::fs::read_to_string(dir.join(format!("{}.rs", module))).expect("read")
    }

    #[test]
    fn an_inbound_fixture_crosses_and_is_asserted_field_by_field() {
        let emitted = emit_inbound("roundtrip", INBOUND);

        assert!(emitted.contains("    let view = fixture_demozoo_query(0);\n"));
        assert!(emitted.contains("    let raw = lower_demozoo_query(&view);\n"));
        assert!(
            emitted.contains("    let read = unsafe { read_demozoo_query(ptr::addr_of!(raw)) };\n")
        );
        assert!(emitted.contains("assert_eq!(read.text, view.text, \"demozoo_query.text\");"));
        // The rename is the host name on both sides; the path still names the def.
        assert!(emitted.contains(
            "assert_eq!(read.categories, view.categories, \"demozoo_query.category_mask\");"
        ));
        assert!(emitted.contains(
            "assert_eq!(read.filter.country, view.filter.country, \"demozoo_query.filter.country\");"
        ));
    }

    /// What only a `[with]` field reaches is never given a fixture at all.
    #[test]
    fn a_with_hatched_field_is_neither_lowered_nor_asserted() {
        let emitted = emit_inbound("hatch", INBOUND);

        assert!(emitted.contains("        tree: Default::default(),\n"));
        assert!(emitted.contains("        entity_mask: Default::default(),\n"));
        // One empty value per shape a hatched field can cross as.
        assert!(emitted.contains("        expr: ptr::null(),\n        expr_count: 0,\n"));
        assert!(emitted.contains("        entity_mask: 0,\n"));
        assert!(emitted.contains("        country: RawStr::EMPTY,\n"));
        assert!(emitted.contains("        order: abi::DemozooSort::Relevance,\n"));

        for hatched in ["expr", "entity_mask", "country", "order"] {
            let assert_line = format!("demozoo_query.{}\"", hatched);
            assert!(!emitted.contains(&assert_line), "{} is asserted", hatched);
        }
        assert!(!emitted.contains("fixture_demozoo_expr_node"));
    }

    #[test]
    fn a_fixed_field_is_neither_seeded_nor_asserted() {
        let emitted = emit("fixed");

        assert!(emitted.contains(
            "fn fixture_demozoo_slot(nth: u32) -> SlotView {\n    SlotView {\n        code:"
        ));
        assert!(
            !emitted.contains("state"),
            "a `[fixed]` field is seeded or asserted"
        );
    }

    /// The whole emitted test body, so dropping an assert fails here rather than
    /// silently shrinking what the generated suite covers.
    #[test]
    fn every_convention_crossed_field_is_asserted() {
        let emitted = emit_inbound("asserts", INBOUND);
        let body = emitted
            .split("fn an_inbound_demozoo_query_reads_back() {\n")
            .nth(1)
            .expect("the round-trip test")
            .split("\n}\n")
            .next()
            .expect("its body");

        assert_eq!(
            body,
            "    let view = fixture_demozoo_query(0);\n\
             \x20   let raw = lower_demozoo_query(&view);\n\
             \x20   // SAFETY: raw addresses view, which outlives the read.\n\
             \x20   let read = unsafe { read_demozoo_query(ptr::addr_of!(raw)) };\n\
             \x20   assert_eq!(read.text, view.text, \"demozoo_query.text\");\n\
             \x20   assert_eq!(read.categories, view.categories, \
             \"demozoo_query.category_mask\");\n\
             \x20   assert_eq!(read.sort, view.sort, \"demozoo_query.sort\");\n\
             \x20   assert_eq!(read.filter.country, view.filter.country, \
             \"demozoo_query.filter.country\");\n\
             \x20   assert_eq!(\n\
             \x20       read.filter.platforms_any,\n\
             \x20       view.filter.platforms_any,\n\
             \x20       \"demozoo_query.filter.platforms_any\",\n\
             \x20   );"
        );
    }

    /// A test that does not compile is worse than no test.
    #[test]
    fn an_unlowerable_root_is_skipped_and_a_nested_record_is_not_one() {
        let src = "\
            #[module(catalog)]\n\
            #[views(crate::catalog::data)]\n\
            struct CatalogTerm { id: u32 }\n\
            struct CatalogQuery {\n\
                terms: *const CatalogTerm,\n\
                term_count: u32,\n\
            }\n\
            api Catalog { rp_catalog_slot_update(q: *const CatalogQuery) -> u32 }";
        let (api_defs, paired) = model_named(src, "catalog.def");
        let inbound = crate::inbound_gen::inbound(&api_defs, &paired);

        assert_eq!(inbound, ["CatalogTerm", "CatalogQuery"], "both are read");
        assert!(
            inbound_roots(&paired, &inbound).is_empty(),
            "a record list cannot be lowered, and `CatalogTerm` is not a root"
        );
    }

    /// The wrong-answer-not-UB guarantee, driven.
    #[test]
    fn an_undeclared_discriminant_is_fed_to_the_reader() {
        let emitted = emit_inbound("bogus", INBOUND);

        assert!(emitted.contains("fn an_undeclared_demozoo_query_sort_reads_the_fallback() {"));
        assert!(emitted.contains(
            "    unsafe { ptr::write(ptr::addr_of_mut!(raw.sort).cast::<u32>(), u32::MAX) };\n"
        ));
        assert!(emitted
            .contains("assert_eq!(read.sort, SortOrder::Relevance, \"demozoo_query.sort\");"));
    }

    #[test]
    fn the_lowering_maps_every_declared_variant_and_falls_back() {
        let emitted = emit_inbound("lower_enum", INBOUND);

        assert!(emitted.contains(
            "        sort: match view.sort {\n\
             \x20           SortOrder::Relevance => abi::DemozooSort::Relevance,\n\
             \x20           SortOrder::TitleAz => abi::DemozooSort::NameAsc,\n\
             \x20           _ => abi::DemozooSort::Relevance,\n\
             \x20       },"
        ));
    }

    /// A record whose every value is fixed never spells nth.
    #[test]
    fn an_enum_field_takes_a_variant_the_zero_value_is_not() {
        let src = "\
            #[module(demozoo)]\n\
            #[views(crate::demoscene::data)]\n\
            #[reads(crate::services::demozoo)]\n\
            #[view(crate::demoscene::query::SortOrder, fallback = TitleAz)]\n\
            enum DemozooSort { NameAsc, [from(TitleZa)] NameDesc }\n\
            #[read]\n\
            struct DemozooOrder { sort: DemozooSort }\n\
            api Demozoo { rp_demozoo_get_order(id: u32) -> DemozooOrder }";
        let (_, paired) = model(src);

        let mut out = Vec::new();
        write_fixture(&mut out, &paired.structs["DemozooOrder"], &paired, false).expect("emit");

        assert_eq!(
            String::from_utf8(out).expect("utf8"),
            "\nfn fixture_demozoo_order(_nth: u32) -> OrderView {\n\
             \x20   OrderView {\n\
             \x20       sort: crate::demoscene::query::SortOrder::TitleZa,\n\
             \x20   }\n\
             }\n"
        );
    }
}
