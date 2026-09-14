# api_gen

An IDL-driven generator. One `.def` file per module describes a C API; api_gen emits the
C header, the raw Rust FFI bindings, an optional ergonomic Rust façade, marshalling and
reader code for a plugin boundary, and the linker export lists (a GNU version script, a
Windows module-def, and optionally a dynamic list).

It is prefix-agnostic: the C type and function prefixes, the include root and prefix, the
export stem and the `use` lines emitted into generated Rust are all configuration. It is
used with several unrelated naming profiles.

## Using it

Depend on it from a **dev-only codegen crate kept in its own workspace**, so api_gen's
dependency tree never reaches the `Cargo.lock` of anything you ship, and call the library
directly — there is no argv in between:

```rust
use api_gen::{naming::Naming, Config};

let summary = api_gen::generate(&Config {
    naming: Naming::new("Fl", "fl"),
    api_dir: repo.join("api"),
    c_include_root: Some(repo.join("include/flowi")),
    c_include_prefix: Some("flowi".to_owned()),
    c_extern_c: true,
    gen_script: Some("cargo regen".to_owned()),
    ..Default::default()
})?;
```

`Config::default()` leaves every output off, so a caller names only the outputs it wants.
`gen_script` is the command named in each generated file's do-not-edit banner; set it to
whatever regenerates *your* project.

The library prints nothing and returns `Result<Summary, Error>`. `Error` covers the
filesystem and a `Config` that asks for an output without the settings that output needs; a
malformed `.def` still panics with a diagnostic, since that is an input bug to fix rather
than a condition to handle.

A `cargo regen` alias in the consumer's `.cargo/config.toml` makes this one command, and a
companion test that regenerates into a temp directory and compares against the committed
files is the drift gate — it never mutates the tree, and it names the file that drifted.

The `api_gen` binary wraps the same `Config` in an argv parser, for callers that would
rather shell out.

## Building against another project's IDL

A project whose defs embed types declared by a library it builds against names that
library's def directory in `reference_dirs`:

```rust
api_gen::generate(&Config {
    api_dir: repo.join("api"),
    reference_dirs: vec![core_checkout.join("api")],
    ..Default::default()
})?;
```

Reference defs are parsed into the type graph — so the layout pass can size a struct that
embeds one of their types by value — and are then excluded from everything that emits. No
header, binding or façade is written for them, they do not appear in the generated `mod.rs`,
and their symbols stay off this project's export list, because the library that owns them
exports them itself. A def present in both directories is an error rather than a silent
shadow: one project owns a def, not both.

Both projects must agree on `c_include_prefix`, since a generated header's cross-include
points at the referenced type's own header.

## Output is deterministic

Regenerating an unchanged tree reproduces byte-identical output, which is what makes the
drift gate above possible. Generated files are meant to be committed.

## Tests

`cargo test` runs the suite, including cases that shell out to `rustc` and to a C compiler
to prove the generated code actually compiles. Those cases **skip themselves** when no
compiler is found, so CI asserts both are present rather than reporting a green, smaller
suite.

## License

MIT — see [LICENSE](LICENSE).
