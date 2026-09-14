//! api_gen as a library: one generate(&Config) entry, driven by a project's own
//! naming + paths.

mod api_parser;
mod c_gen;
mod emit_util;
mod inbound_gen;
mod layout;
mod marshal_gen;
pub mod naming;
pub mod pairing;
mod read_gen;
mod rust_gen;
mod test_gen;

#[macro_use]
extern crate pest_derive;

use crate::api_parser::{ApiDef, ApiParser};
use crate::c_gen::Cgen;
use crate::naming::Naming;
use crate::rust_gen::RustGen;
use std::collections::BTreeSet;
use std::io::Write;
use std::path::{Path, PathBuf};

/// What a [`generate`] call could not do.
///
/// Covers the failures a caller can act on: the filesystem, and a [`Config`] that asks for an
/// output without the settings that output needs. A malformed `.def` still panics with a
/// diagnostic — that is an input bug to fix, not a condition to handle.
#[derive(Debug)]
pub enum Error {
    /// A filesystem operation failed. `doing` says what was being attempted.
    Io {
        /// What api_gen was doing, e.g. "creating" or "writing the C header for cursor".
        doing: String,
        /// The path it was doing it to.
        path: PathBuf,
        /// The underlying failure.
        source: std::io::Error,
    },
    /// The `Config` is internally inconsistent.
    Config(String),
    /// The IDL does not describe a consistent API.
    Idl(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Io {
                doing,
                path,
                source,
            } => {
                write!(f, "{} {}: {}", doing, path.display(), source)
            }
            Error::Config(msg) | Error::Idl(msg) => f.write_str(msg),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// What a [`generate`] call produced. Nothing is printed by the library; a caller that wants
/// progress on stdout formats this.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Summary {
    /// How many `.def` modules were processed.
    pub modules: usize,
    /// How many symbols the export list names, or 0 when no export dir was configured.
    pub exported_symbols: usize,
}

/// Tag an io error with what was being attempted and where.
fn io(doing: &str, path: &Path) -> impl FnOnce(std::io::Error) -> Error {
    let doing = doing.to_owned();
    let path = path.to_path_buf();
    move |source| Error::Io {
        doing,
        path,
        source,
    }
}

/// api_gen's emitters take `&str` paths, so a non-UTF-8 output dir is a config error.
fn utf8(path: &Path) -> Result<&str, Error> {
    path.to_str()
        .ok_or_else(|| Error::Config(format!("path is not valid UTF-8: {}", path.display())))
}

/// One project's codegen target: naming profile + input/output paths.
///
/// `Default` leaves every output off, so a caller names only the outputs it wants:
///
/// ```no_run
/// # use api_gen::{Config, naming::Naming};
/// api_gen::generate(&Config {
///     naming: Naming::new("Fl", "fl"),
///     api_dir: "api".into(),
///     c_include_root: Some("include/flowi".into()),
///     ..Default::default()
/// });
/// ```
#[derive(Debug, Clone, Default)]
pub struct Config {
    pub naming: Naming,
    /// Input defs: `<api_dir>/*.def`. These are the defs this run owns and emits.
    pub api_dir: PathBuf,
    /// Extra def directories parsed for their types but never emitted: the IDL of a
    /// library this project builds against. A def in `api_dir` may embed a type
    /// declared here by value, and the layout pass needs its size to resolve the
    /// embedder - but the header, binding and exported symbol for it belong to
    /// whoever owns that library, and emitting a second copy here would be the two-
    /// copies problem this exists to avoid.
    ///
    /// Cross-module C includes still point at the referenced type's own header, so
    /// the two projects must agree on `c_include_prefix`.
    pub reference_dirs: Vec<PathBuf>,
    /// Raw Rust FFI output dir (Flowi: rust/flowi_sys/src/generated).
    pub rust_dir: Option<PathBuf>,
    /// C public-header root; per-module subdir created on demand.
    pub c_include_root: Option<PathBuf>,
    /// Ergonomic Rust façade output dir. None skips façade generation.
    pub facade_dir: Option<PathBuf>,
    /// Output dir for the generated service-consume wrapper crate: one
    /// `<def>.rs` module per `#[attributes(service)]` def plus a mod.rs index.
    /// None skips wrapper generation.
    pub service_wrapper_dir: Option<PathBuf>,
    /// Module path, in the consumer crate, of the raw --rust-dir bindings tree
    /// (crate::generated). When set, a wrapper module forwards through those
    /// declarations - `crate::generated::<def>::<symbol>(...)` - instead of declaring
    /// its own extern "C" block. None keeps the self-contained module, the only
    /// option for a consumer that generates no raw tree.
    pub service_wrapper_raw_path: Option<String>,
    /// C cross-include prefix for a referenced type's own header.
    /// Some("flowi") -> `#include <flowi/<module>/x.h>`;
    /// None -> `#include "x.h"` (same-dir, no framework path).
    pub c_include_prefix: Option<String>,
    /// Wrap the generated C declarations in an extern "C" block so a shared
    /// header links correctly from C and C++.
    pub c_extern_c: bool,
    /// Output dir for the curated linker export list: the GNU version script
    /// (flowi.version) and the Windows module-def (flowi.def) naming exactly
    /// the public C symbols the shared library exports. None skips export-list
    /// generation.
    pub export_dir: Option<PathBuf>,
    /// Stem of the export-list files and the version-script node
    /// (flowi -> flowi.version / flowi.def / FLOWI_1.0). None keeps
    /// the flowi default.
    pub export_stem: Option<String>,
    /// Emit the version script without the `local: *;` catch-all, so the listed
    /// symbols are added to whatever else is already dynamically visible rather
    /// than curating the whole set.
    pub export_additive: bool,
    /// Emit static_assert layout pins (struct size + field offsets) into each
    /// generated C header, the C counterpart of the const _ block the Rust
    /// binding always carries. Opt-in: it changes previously emitted headers.
    pub c_layout_asserts: bool,
    /// Also emit the export set as a GNU linker dynamic list
    /// (`<stem>.dynlist`, -Wl,--dynamic-list= format), which an executable
    /// exporting to dlopen'd plugins uses instead of a version script.
    pub export_dynlist: bool,
    /// Output dir for the host-side publish marshalling: one `<def>_marshal.rs` per
    /// def whose types pair with host views, plus a mod.rs index. None skips
    /// marshal generation.
    pub marshal_dir: Option<PathBuf>,
    /// Crate the emitted marshalling names the raw ABI types through
    /// (replay_plugin -> `use replay_plugin::<def> as abi;`).
    pub marshal_abi_crate: Option<String>,
    /// Verbatim use paths the emitted marshalling needs: the arena type, the
    /// string-into-arena type, and the array-publishing helper.
    pub marshal_uses: Vec<String>,
    /// Verbatim use paths the emitted inbound readers need: the slice-borrowing
    /// helper. Kept apart from marshal_uses - an unused import is a warning in
    /// the consumer's lane.
    pub inbound_uses: Vec<String>,
    /// Output dir for the consume-side readers: one `<def>_read.rs` per def with
    /// `#[read]` records. Emitted into the raw-bindings tree, so --rust-dir
    /// declares them. None skips read generation.
    pub read_dir: Option<PathBuf>,
    /// Module path, in the consumer crate, of the raw bindings tree the readers
    /// name the ABI types through (crate::generated).
    pub read_abi_path: Option<String>,
    /// Verbatim use paths the emitted readers need: the slice-borrowing helper.
    pub read_uses: Vec<String>,
    /// Cargo feature that turns the reader modules public. Off in a real plugin
    /// build; the tests that drive a reader directly enable it.
    pub read_test_feature: Option<String>,
    /// Module path, in the crate the marshalling is emitted into, of the reader
    /// modules the round-trip tests read back through (replay_plugin::generated).
    /// None skips test generation.
    pub test_read_path: Option<String>,
    /// Arena type the round-trip tests publish into: `<type>::new(bytes)` reserves
    /// one and as_raw() answers the raw pointer.
    pub test_arena: Option<String>,
    /// Script the emitted marshalling and readers name as the way to regenerate.
    /// None keeps the generic wording.
    pub gen_script: Option<String>,
    /// Emit `#![allow(dead_code)]` atop each generated Rust tree's mod.rs. A sys
    /// mirror of a full C API wants it; a consumer whose defs are 1:1 with its Rust
    /// surface leaves it off so an orphaned binding is a warning.
    pub rust_allow_dead_code: bool,
}

fn gen_script(cfg: &Config) -> &str {
    cfg.gen_script
        .as_deref()
        .unwrap_or("the project's binding script")
}

/// Every `*.def` under `dir`, sorted, so a run's parse order never depends on the
/// filesystem's.
fn defs_in(dir: &Path) -> Result<Vec<PathBuf>, Error> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(io("reading", dir))?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map(|x| x == "def").unwrap_or(false))
        .collect();
    files.sort();
    Ok(files)
}

pub fn generate(cfg: &Config) -> Result<Summary, Error> {
    let api_dir = &cfg.api_dir;
    if let Some(c_include_root) = &cfg.c_include_root {
        std::fs::create_dir_all(c_include_root).map_err(io("creating", c_include_root))?;
    }
    if let Some(rust_dir) = &cfg.rust_dir {
        std::fs::create_dir_all(rust_dir).map_err(io("creating", rust_dir))?;
    }
    if let Some(facade) = &cfg.facade_dir {
        std::fs::create_dir_all(facade).map_err(io("creating", facade))?;
    }
    if let Some(wrapper_dir) = &cfg.service_wrapper_dir {
        std::fs::create_dir_all(wrapper_dir).map_err(io("creating", wrapper_dir))?;
    }

    let files = defs_in(api_dir)?;
    let mut api_defs: Vec<ApiDef> = Vec::with_capacity(files.len());
    for path in &files {
        let mut api_def = ApiDef::default();
        ApiParser::parse_file(path, &mut api_def);
        api_defs.push(api_def);
    }

    // Reference defs join the type graph so the passes below see every type, then drop
    // out of every emission loop: `owned` is the set this run is allowed to write for.
    // A reference def that repeats a name from api_dir is a real conflict - two projects
    // both claiming one type - so it is rejected rather than silently shadowed.
    let owned: std::collections::HashSet<String> =
        api_defs.iter().map(|d| d.base_filename.clone()).collect();
    for dir in &cfg.reference_dirs {
        for path in &defs_in(dir)? {
            let mut api_def = ApiDef::default();
            ApiParser::parse_file(path, &mut api_def);
            if owned.contains(&api_def.base_filename) {
                return Err(Error::Config(format!(
                    "reference def {} also exists in api_dir {}; one project owns a def, \
                     not both",
                    path.display(),
                    api_dir.display()
                )));
            }
            api_defs.push(api_def);
        }
    }

    ApiParser::second_pass(&mut api_defs, &cfg.naming);
    api_defs.sort_by(|a, b| a.filename.cmp(&b.filename));

    // Everything downstream that EMITS walks this; everything that RESOLVES walks
    // api_defs.
    let emitted: Vec<&ApiDef> = api_defs
        .iter()
        .filter(|d| owned.contains(&d.base_filename))
        .collect();

    let paired = pairing::resolve(&api_defs).map_err(|e| Error::Idl(e.to_string()))?;
    if let Some(marshal_dir) = &cfg.marshal_dir {
        let dir = utf8(marshal_dir)?;
        std::fs::create_dir_all(marshal_dir).map_err(io("creating", marshal_dir))?;
        let publishable = marshal_gen::publishable(&emitted, &paired);
        let abi_crate = cfg
            .marshal_abi_crate
            .as_deref()
            .ok_or_else(|| Error::Config("marshal_dir needs marshal_abi_crate".to_owned()))?;
        let mut modules = marshal_gen::generate(
            dir,
            &publishable,
            &paired,
            &marshal_gen::MarshalPaths {
                abi_crate,
                uses: &cfg.marshal_uses,
                script: gen_script(cfg),
            },
        )
        .map_err(io("writing marshalling into", marshal_dir))?;

        let inbound = inbound_gen::inbound(&emitted, &paired);
        modules.extend(
            inbound_gen::generate(
                dir,
                &inbound,
                &paired,
                &inbound_gen::InboundPaths {
                    abi_crate,
                    uses: &cfg.inbound_uses,
                    script: gen_script(cfg),
                },
            )
            .map_err(io("writing inbound readers into", marshal_dir))?,
        );

        let mut tests = match &cfg.test_read_path {
            Some(read_path) => test_gen::generate(
                dir,
                &paired,
                &publishable,
                &test_gen::TestPaths {
                    read_path,
                    arena: cfg.test_arena.as_deref().ok_or_else(|| {
                        Error::Config("test_read_path needs test_arena".to_owned())
                    })?,
                    script: gen_script(cfg),
                },
            )
            .map_err(io("writing round-trip tests into", marshal_dir))?,
            None => Vec::new(),
        };
        tests.extend(
            test_gen::generate_inbound(
                dir,
                &paired,
                &inbound,
                &test_gen::InboundTestPaths {
                    abi_crate,
                    uses: &cfg.marshal_uses,
                    script: gen_script(cfg),
                },
            )
            .map_err(io("writing inbound round-trip tests into", marshal_dir))?,
        );

        marshal_gen::write_mod_file(dir, &modules, &tests, gen_script(cfg))
            .map_err(io("writing mod.rs into", marshal_dir))?;
    }

    let mut read_modules = Vec::new();
    if let Some(read_dir) = &cfg.read_dir {
        std::fs::create_dir_all(read_dir).map_err(io("creating", read_dir))?;
        read_modules = read_gen::generate(
            utf8(read_dir)?,
            &paired,
            &read_gen::ReadPaths {
                abi_path: cfg
                    .read_abi_path
                    .as_deref()
                    .ok_or_else(|| Error::Config("read_dir needs read_abi_path".to_owned()))?,
                uses: &cfg.read_uses,
                script: gen_script(cfg),
            },
        )
        .map_err(io("writing readers into", read_dir))?;
    }

    let registry = layout::TypeRegistry::build(&api_defs);

    let mut type_loc: std::collections::BTreeMap<String, (String, String)> =
        std::collections::BTreeMap::new();
    for api_def in &api_defs {
        let loc = (api_def.module.clone(), api_def.base_filename.clone());
        for sdef in &api_def.structs {
            type_loc.insert(sdef.name.clone(), loc.clone());
        }
        for edef in &api_def.enums {
            type_loc.insert(edef.name.clone(), loc.clone());
        }
        for cb in &api_def.callbacks {
            type_loc.insert(cb.name.clone(), loc.clone());
        }
    }

    if let Some(rust_dir) = &cfg.rust_dir {
        RustGen::generate_mod_file(
            utf8(rust_dir)?,
            &emitted,
            cfg.rust_allow_dead_code,
            &read_modules,
            cfg.read_test_feature.as_deref(),
            gen_script(cfg),
        )
        .map_err(io("writing mod.rs into", rust_dir))?;
    }

    // The readers a wrapper delegates to sit beside the raw modules the same path
    // names, so the read side needs no path of its own.
    let service_reads = cfg
        .read_abi_path
        .as_deref()
        .map(|path| rust_gen::ServiceReads {
            model: &paired,
            path,
        });

    let mut facade_modules: Vec<String> = Vec::new();
    let mut service_wrapper_modules: Vec<String> = Vec::new();
    for api_def in &emitted {
        if let Some(rust_dir) = &cfg.rust_dir {
            RustGen::generate(utf8(rust_dir)?, api_def, &registry, gen_script(cfg)).map_err(io(
                &format!("writing Rust for {} into", api_def.base_filename),
                rust_dir,
            ))?;
        }
        // A service def with an unclassifiable slot hard-fails here by design.
        if let Some(wrapper_dir) = &cfg.service_wrapper_dir {
            if RustGen::generate_service_wrapper(
                utf8(wrapper_dir)?,
                api_def,
                &cfg.naming,
                cfg.service_wrapper_raw_path.as_deref(),
                service_reads.as_ref(),
                gen_script(cfg),
            )
            .map_err(io(
                &format!(
                    "writing the service wrapper for {} into",
                    api_def.base_filename
                ),
                wrapper_dir,
            ))? {
                service_wrapper_modules.push(api_def.base_filename.clone());
            }
        }
        if let Some(facade) = &cfg.facade_dir {
            if RustGen::generate_facade(utf8(facade)?, api_def, gen_script(cfg)).map_err(io(
                &format!("writing the façade for {} into", api_def.base_filename),
                facade,
            ))? {
                facade_modules.push(api_def.base_filename.clone());
            }
        }
        if let Some(c_include_root) = &cfg.c_include_root {
            if api_def.has_real_types() || api_def.has_apis() || api_def.has_callbacks() {
                // Every def emits the real-type header plus `fl_*` prototypes and call
                // macros; a `#[attributes(service)]` def exports its slots under their
                // raw slot names instead.
                Cgen::generate_header(
                    utf8(c_include_root)?,
                    api_def,
                    &type_loc,
                    &cfg.naming,
                    cfg.c_include_prefix.as_deref(),
                    cfg.c_extern_c,
                    cfg.c_layout_asserts.then_some(&registry),
                    gen_script(cfg),
                )
                .map_err(io(
                    &format!("writing the C header for {} into", api_def.base_filename),
                    c_include_root,
                ))?;
            }
        }
    }

    if let Some(facade) = &cfg.facade_dir {
        RustGen::generate_facade_mod_file(
            utf8(facade)?,
            &facade_modules,
            cfg.rust_allow_dead_code,
            gen_script(cfg),
        )
        .map_err(io("writing façade mod.rs into", facade))?;
    }

    if let Some(wrapper_dir) = &cfg.service_wrapper_dir {
        RustGen::generate_service_wrapper_mod_file(
            utf8(wrapper_dir)?,
            &service_wrapper_modules,
            cfg.rust_allow_dead_code,
            gen_script(cfg),
        )
        .map_err(io("writing service-wrapper mod.rs into", wrapper_dir))?;
    }

    let mut exported_symbols = 0;
    if let Some(export_dir) = &cfg.export_dir {
        let stem = cfg.export_stem.as_deref().unwrap_or("flowi");
        exported_symbols = write_export_list(
            export_dir,
            stem,
            cfg.export_additive,
            cfg.export_dynlist,
            &emitted,
            gen_script(cfg),
        )
        .map_err(io("writing the export list into", export_dir))?;
    }

    Ok(Summary {
        modules: emitted.len(),
        exported_symbols,
    })
}

/// Collect the public C symbol set the shared library exports and write it as both
/// a GNU linker version script (`<stem>.version`) and a Windows module-def
/// (`<stem>.def`) into export_dir, plus a GNU dynamic list (`<stem>.dynlist`)
/// when dynlist is set. The set is exactly every api block function's c_name -
/// including the variadic ones, which Rust cannot declare.
fn write_export_list(
    export_dir: &Path,
    export_stem: &str,
    additive: bool,
    dynlist: bool,
    api_defs: &[&ApiDef],
    script: &str,
) -> std::io::Result<usize> {
    std::fs::create_dir_all(export_dir)?;

    let mut symbols: BTreeSet<String> = BTreeSet::new();
    for api_def in api_defs {
        for api in &api_def.apis {
            for func in &api.functions {
                symbols.insert(func.c_name.clone());
            }
        }
    }

    let banner = format!(
        "@generated by api_gen - DO NOT EDIT. Regenerate with {}.",
        script
    );

    let version_path = export_dir.join(format!("{}.version", export_stem));
    let mut vf = std::io::BufWriter::new(std::fs::File::create(&version_path)?);
    writeln!(vf, "/* {} */", banner)?;
    writeln!(vf, "{}_1.0 {{", export_stem.to_uppercase())?;
    writeln!(vf, "  global:")?;
    for sym in &symbols {
        writeln!(vf, "    {};", sym)?;
    }
    if !additive {
        writeln!(vf, "  local:")?;
        writeln!(vf, "    *;")?;
    }
    writeln!(vf, "}};")?;

    let def_path = export_dir.join(format!("{}.def", export_stem));
    let mut df = std::io::BufWriter::new(std::fs::File::create(&def_path)?);
    writeln!(df, "; {}", banner)?;
    writeln!(df, "EXPORTS")?;
    for sym in &symbols {
        writeln!(df, "    {}", sym)?;
    }

    if dynlist {
        let dynlist_path = export_dir.join(format!("{}.dynlist", export_stem));
        let mut lf = std::io::BufWriter::new(std::fs::File::create(&dynlist_path)?);
        writeln!(lf, "/* {} */", banner)?;
        writeln!(lf, "{{")?;
        for sym in &symbols {
            writeln!(lf, "  {};", sym)?;
        }
        writeln!(lf, "}};")?;
    }

    Ok(symbols.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn service_wrapper_pass_needs_no_other_output_trees() {
        let root = std::env::temp_dir().join(format!(
            "api_gen_wrapper_only_{}_{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let api_dir = root.join("api");
        let wrapper_dir = root.join("wrappers");
        std::fs::create_dir_all(&api_dir).expect("create api dir");
        std::fs::write(
            api_dir.join("probe.def"),
            "#[attributes(service)] api Probe { probe_depth() -> u32 }",
        )
        .expect("write fixture");

        let summary = generate(&Config {
            naming: crate::naming::FL,
            api_dir,
            reference_dirs: Vec::new(),
            rust_dir: None,
            c_include_root: None,
            facade_dir: None,
            service_wrapper_dir: Some(wrapper_dir.clone()),
            service_wrapper_raw_path: None,
            c_include_prefix: None,
            c_extern_c: false,
            c_layout_asserts: false,
            export_dir: None,
            export_stem: None,
            export_additive: false,
            export_dynlist: false,
            marshal_dir: None,
            marshal_abi_crate: None,
            marshal_uses: Vec::new(),
            inbound_uses: Vec::new(),
            read_dir: None,
            read_abi_path: None,
            read_uses: Vec::new(),
            read_test_feature: None,
            test_read_path: None,
            test_arena: None,
            gen_script: None,
            rust_allow_dead_code: false,
        })
        .expect("wrapper-only generation");
        assert_eq!(summary.modules, 1);

        assert!(wrapper_dir.join("probe.rs").is_file());
        assert!(wrapper_dir.join("mod.rs").is_file());
        assert_eq!(
            std::fs::read_dir(&root).expect("read temp root").count(),
            2,
            "wrapper-only generation must not create discarded C or raw-Rust trees"
        );
        let _ = std::fs::remove_dir_all(root);
    }

    /// A library's defs join the type graph without being emitted: the embedder's own
    /// header and binding resolve the borrowed type's layout, but nothing is written for
    /// it and its symbols stay off this project's export list.
    #[test]
    fn reference_defs_resolve_layout_without_being_emitted() {
        let root = std::env::temp_dir().join(format!(
            "api_gen_reference_{}_{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let api_dir = root.join("api");
        let ref_dir = root.join("vendor-api");
        let rust_dir = root.join("rust");
        let include_root = root.join("include");
        let export_dir = root.join("exports");
        std::fs::create_dir_all(&api_dir).expect("create api dir");
        std::fs::create_dir_all(&ref_dir).expect("create reference dir");

        // The library owns Vec2; the embedder embeds it by value, so its own layout is
        // unresolvable unless the reference def is parsed.
        std::fs::write(
            ref_dir.join("math_data.def"),
            "struct Vec2 { x: f32, y: f32 }\napi Math { math_len(v: Vec2) -> f32 }",
        )
        .expect("write reference fixture");
        std::fs::write(
            api_dir.join("widget.def"),
            "struct WidgetBox { origin: Vec2, size: Vec2 }\n\
             api Widget { widget_emit(b: WidgetBox) -> u32 }",
        )
        .expect("write owned fixture");

        let summary = generate(&Config {
            naming: crate::naming::FL,
            api_dir,
            reference_dirs: vec![ref_dir],
            rust_dir: Some(rust_dir.clone()),
            c_include_root: Some(include_root.clone()),
            export_dir: Some(export_dir.clone()),
            c_layout_asserts: true,
            ..Default::default()
        })
        .expect("generation with a reference def");

        // Only the owned def counts as a module, and only its symbol is exported.
        assert_eq!(summary.modules, 1, "the reference def is not a module here");
        assert_eq!(
            summary.exported_symbols, 1,
            "math_len belongs to the library"
        );

        assert!(rust_dir.join("widget.rs").is_file());
        assert!(
            !rust_dir.join("math_data.rs").exists(),
            "a reference def must not be emitted"
        );
        assert!(!include_root.join("math_data/math_data.h").exists());

        let mod_rs = std::fs::read_to_string(rust_dir.join("mod.rs")).expect("read mod.rs");
        assert!(mod_rs.contains("widget"));
        assert!(
            !mod_rs.contains("math_data"),
            "the index must not declare a module that was never written"
        );

        // The borrowed type resolved: WidgetBox is two Vec2s, so 16 bytes.
        let widget_rs = std::fs::read_to_string(rust_dir.join("widget.rs")).expect("read widget");
        assert!(
            widget_rs.contains("size_of::<WidgetBox>() == 16"),
            "the embedder's layout must resolve through the reference def:\n{widget_rs}"
        );

        let version = std::fs::read_to_string(export_dir.join("flowi.version")).expect("exports");
        assert!(version.contains("widget_emit;"));
        assert!(
            !version.contains("math_len;"),
            "a reference def's symbols are exported by whoever owns it"
        );

        let _ = std::fs::remove_dir_all(root);
    }

    /// Two projects cannot both own one def. Shadowing silently would make which copy
    /// wins depend on directory order.
    #[test]
    fn a_reference_def_may_not_shadow_an_owned_one() {
        let root = std::env::temp_dir().join(format!(
            "api_gen_reference_clash_{}_{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let api_dir = root.join("api");
        let ref_dir = root.join("vendor-api");
        std::fs::create_dir_all(&api_dir).expect("create api dir");
        std::fs::create_dir_all(&ref_dir).expect("create reference dir");
        std::fs::write(
            api_dir.join("math_data.def"),
            "struct Vec2 { x: f32, y: f32 }",
        )
        .expect("write owned fixture");
        std::fs::write(
            ref_dir.join("math_data.def"),
            "struct Vec2 { x: f32, y: f32 }",
        )
        .expect("write reference fixture");

        let err = generate(&Config {
            naming: crate::naming::FL,
            api_dir,
            reference_dirs: vec![ref_dir],
            rust_dir: Some(root.join("rust")),
            ..Default::default()
        })
        .expect_err("a def owned on both sides must be rejected");
        assert!(
            matches!(err, Error::Config(ref m) if m.contains("math_data.def")),
            "unexpected error: {err}"
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn export_list_includes_variadic_api_functions() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api Format { frame_string(fmt: *const char, ...) -> String }",
            "format.def",
            &mut api_def,
        );
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);

        let export_dir =
            std::env::temp_dir().join(format!("api_gen_exports_{}", std::process::id()));
        std::fs::create_dir_all(&export_dir).expect("create export temp dir");
        write_export_list(
            &export_dir,
            "flowi",
            false,
            false,
            &crate::pairing::as_refs(&api_defs),
            "scripts/gen.sh",
        )
        .expect("write export list");
        let version = std::fs::read_to_string(export_dir.join("flowi.version"))
            .expect("read generated version script");
        let _ = std::fs::remove_dir_all(&export_dir);

        assert!(
            version.contains("    fl_format_frame_string;"),
            "a public variadic declaration must name a real exported symbol"
        );
    }

    #[test]
    fn export_list_contains_only_idl_symbols() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api Frame { set_alpha(alpha: u8) }",
            "frame.def",
            &mut api_def,
        );
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);

        let export_dir =
            std::env::temp_dir().join(format!("api_gen_idl_exports_{}", std::process::id()));
        std::fs::create_dir_all(&export_dir).expect("create export temp dir");
        write_export_list(
            &export_dir,
            "flowi",
            false,
            false,
            &crate::pairing::as_refs(&api_defs),
            "scripts/gen.sh",
        )
        .expect("write export list");
        let module_def = std::fs::read_to_string(export_dir.join("flowi.def"))
            .expect("read generated module definition");
        let _ = std::fs::remove_dir_all(&export_dir);

        assert_eq!(
            module_def,
            "; @generated by api_gen - DO NOT EDIT. Regenerate with scripts/gen.sh.\nEXPORTS\n    fl_frame_set_alpha\n"
        );
    }

    #[test]
    fn export_dynlist_is_opt_in_and_matches_symbol_set() {
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "api Frame { set_alpha(alpha: u8) }",
            "frame.def",
            &mut api_def,
        );
        let mut api_defs = vec![api_def];
        ApiParser::second_pass(&mut api_defs, &crate::naming::FL);

        let export_dir =
            std::env::temp_dir().join(format!("api_gen_dynlist_exports_{}", std::process::id()));
        std::fs::create_dir_all(&export_dir).expect("create export temp dir");

        write_export_list(
            &export_dir,
            "flowi",
            true,
            false,
            &crate::pairing::as_refs(&api_defs),
            "scripts/gen.sh",
        )
        .expect("write export list");
        assert!(
            !export_dir.join("flowi.dynlist").exists(),
            "dynlist emission must stay opt-in"
        );

        write_export_list(
            &export_dir,
            "flowi",
            true,
            true,
            &crate::pairing::as_refs(&api_defs),
            "scripts/gen.sh",
        )
        .expect("write export list");
        let dynlist = std::fs::read_to_string(export_dir.join("flowi.dynlist"))
            .expect("read generated dynamic list");
        let _ = std::fs::remove_dir_all(&export_dir);

        assert_eq!(
            dynlist,
            "/* @generated by api_gen - DO NOT EDIT. Regenerate with scripts/gen.sh. */\n{\n  fl_frame_set_alpha;\n};\n"
        );
    }
}
