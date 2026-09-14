//! api_gen entry point - builds Config from CLI args and delegates to the lib.
//! Paths are taken verbatim (absolute or cwd-relative).

use api_gen::{generate, naming::Naming, Config};
use std::path::PathBuf;

fn main() {
    let mut args = std::env::args().skip(1);
    let mut naming = None;
    let mut api_dir = None;
    let mut rust_dir = None;
    let mut c_include_root = None;
    let mut facade_dir = None;
    let mut service_wrapper_dir = None;
    let mut service_wrapper_raw_path = None;
    let mut c_include_prefix = None;
    let mut c_extern_c = false;
    let mut c_layout_asserts = false;
    let mut export_dir = None;
    let mut c_string_type = None;
    let mut c_string_include = None;
    let mut export_stem = None;
    let mut export_additive = false;
    let mut export_dynlist = false;
    let mut rust_allow_dead_code = false;
    let mut marshal_dir = None;
    let mut marshal_abi_crate = None;
    let mut marshal_uses = Vec::new();
    let mut inbound_uses = Vec::new();
    let mut gen_script = None;
    let mut read_dir = None;
    let mut read_abi_path = None;
    let mut read_uses = Vec::new();
    let mut read_test_feature = None;
    let mut test_read_path = None;
    let mut test_arena = None;

    while let Some(arg) = args.next() {
        let mut val = || {
            args.next()
                .unwrap_or_else(|| panic!("missing value for {arg}"))
        };
        match arg.as_str() {
            "--naming" => {
                let v = val();
                let (t, f) = v.split_once(',').expect("--naming wants TYPE,FUNC");
                naming = Some(Naming::new(t, f));
            }
            "--api-dir" => api_dir = Some(PathBuf::from(val())),
            "--rust-dir" => rust_dir = Some(PathBuf::from(val())),
            "--c-include-root" => c_include_root = Some(PathBuf::from(val())),
            "--facade-dir" => facade_dir = Some(PathBuf::from(val())),
            "--service-wrapper-dir" => service_wrapper_dir = Some(PathBuf::from(val())),
            "--service-wrapper-raw-path" => service_wrapper_raw_path = Some(val()),
            "--c-include-prefix" => c_include_prefix = Some(val()),
            "--c-extern-c" => c_extern_c = true,
            "--c-layout-asserts" => c_layout_asserts = true,
            "--export-dir" => export_dir = Some(PathBuf::from(val())),
            "--c-string-type" => c_string_type = Some(val()),
            "--c-string-include" => c_string_include = Some(val()),
            "--export-stem" => export_stem = Some(val()),
            "--export-additive" => export_additive = true,
            "--export-dynlist" => export_dynlist = true,
            "--rust-allow-dead-code" => rust_allow_dead_code = true,
            "--marshal-dir" => marshal_dir = Some(PathBuf::from(val())),
            "--marshal-abi-crate" => marshal_abi_crate = Some(val()),
            "--marshal-use" => marshal_uses.push(val()),
            "--inbound-use" => inbound_uses.push(val()),
            "--gen-script" => gen_script = Some(val()),
            "--read-dir" => read_dir = Some(PathBuf::from(val())),
            "--read-abi-path" => read_abi_path = Some(val()),
            "--read-use" => read_uses.push(val()),
            "--read-test-feature" => read_test_feature = Some(val()),
            "--test-read-path" => test_read_path = Some(val()),
            "--test-arena" => test_arena = Some(val()),
            other => panic!("unknown arg: {other}"),
        }
    }

    let mut naming = naming.expect("--naming required");
    if let Some(t) = c_string_type {
        naming.string_type = Some(std::borrow::Cow::Owned(t));
    }
    if let Some(p) = c_string_include {
        naming.string_include = Some(std::borrow::Cow::Owned(p));
    }

    // The library prints nothing and returns its failures; the CLI is what reports both.
    let summary = match generate(&Config {
        naming,
        api_dir: api_dir.expect("--api-dir required"),
        rust_dir,
        c_include_root,
        facade_dir,
        service_wrapper_dir,
        service_wrapper_raw_path,
        c_include_prefix,
        c_extern_c,
        c_layout_asserts,
        export_dir,
        export_stem,
        export_additive,
        export_dynlist,
        marshal_dir,
        marshal_abi_crate,
        marshal_uses,
        inbound_uses,
        read_dir,
        read_abi_path,
        read_uses,
        read_test_feature,
        test_read_path,
        test_arena,
        gen_script,
        rust_allow_dead_code,
    }) {
        Ok(summary) => summary,
        Err(e) => {
            eprintln!("api_gen: {e}");
            std::process::exit(1);
        }
    };

    if summary.exported_symbols > 0 {
        println!(
            "api_gen: wrote {} exported symbol(s)",
            summary.exported_symbols
        );
    }
    println!("api_gen: processed {} module(s)", summary.modules);
}
