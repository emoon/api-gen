//! References between items in doc comments. A `.def` comment names another item by
//! its IDL spelling in backticks; the C header shows the name a C caller writes, the
//! raw Rust bindings show the linked C name, and the Rust façade shows the Rust name
//! of a function whose method is named otherwise.

use crate::api_parser::{Api, ApiDef, Enum, Struct};
use crate::naming::Naming;
use crate::rust_gen::RustGen;
use std::collections::{HashMap, HashSet};

/// Every item a doc comment can name, with its C spelling and, where one is given,
/// its Rust spelling.
#[derive(Debug, Default)]
pub struct DocRefs {
    /// IDL reference (`List::begin`, `ListResult`, `ListResult.requests`) to C spelling.
    c_names: HashMap<String, String>,
    /// IDL reference to Rust spelling, for the api functions whose façade method has
    /// another name: the ones marked `[rust_doc]` and the generated `_impl` ones.
    rust_names: HashMap<String, String>,
    /// IDL reference to the C function the raw Rust bindings declare for it.
    sys_names: HashMap<String, String>,
    /// Names of the types and api blocks, which own the members a reference can name.
    owners: HashSet<String>,
}

impl DocRefs {
    pub fn new(api_defs: &[ApiDef], naming: &Naming) -> DocRefs {
        let mut refs = DocRefs::default();
        refs.c_names
            .insert("String".to_owned(), naming.c_string_type());
        for def in api_defs {
            for s in &def.structs {
                refs.add_struct(s, naming);
            }
            for e in &def.enums {
                refs.add_enum(e, naming);
            }
            for api in &def.apis {
                refs.owners.insert(api.name.clone());
                refs.add_rust_names(api);
                for func in &api.functions {
                    let idl_name = format!("{}::{}", api.name, func.name);
                    if RustGen::raw_declares(func) {
                        refs.sys_names.insert(idl_name.clone(), func.c_name.clone());
                    }
                    refs.c_names
                        .insert(idl_name, crate::c_gen::c_call_name(api, func));
                }
            }
            for cb in &def.callbacks {
                refs.add_type(&cb.name, naming.c_type(&cb.name));
            }
            for ext in &def.externs {
                refs.add_type(&ext.name, ext.name.clone());
            }
        }
        refs
    }

    fn add_type(&mut self, name: &str, c_name: String) {
        self.owners.insert(name.to_owned());
        self.c_names.insert(name.to_owned(), c_name);
    }

    fn add_struct(&mut self, s: &Struct, naming: &Naming) {
        let c_type = naming.c_type(&s.name);
        for var in struct_fields(s) {
            self.c_names.insert(
                format!("{}.{}", s.name, var.name),
                format!("{}.{}", c_type, var.name),
            );
        }
        // A struct's function is a function-pointer field in C.
        for func in &s.functions {
            self.c_names.insert(
                format!("{}::{}", s.name, func.name),
                format!("{}.{}", c_type, func.name),
            );
        }
        self.add_type(&s.name, c_type);
    }

    fn add_enum(&mut self, e: &Enum, naming: &Naming) {
        let stem = e.enumerator_override.as_deref().unwrap_or(&e.name);
        for entry in &e.entries {
            self.c_names.insert(
                format!("{}::{}", e.name, entry.name),
                naming.c_enumerator(stem, &entry.name),
            );
        }
        self.add_type(&e.name, naming.c_type(&e.name));
    }

    /// The references in def's doc comments that name a member its owner does not
    /// have, one message per reference. Empty means every reference resolves.
    pub fn unresolved(&self, def: &ApiDef) -> Vec<String> {
        let mut missing = Vec::new();
        for (item, comments) in doc_blocks(def) {
            for (span, quoted) in comments.iter().flat_map(|line| spans(line)) {
                if quoted && self.is_unresolved(span) {
                    missing.push(format!("  {item}: `{span}`"));
                }
            }
        }
        missing
    }

    fn is_unresolved(&self, span: &str) -> bool {
        let name = call_target(span);
        match member_owner(name) {
            Some(owner) => self.owners.contains(owner) && !self.c_names.contains_key(name),
            None => false,
        }
    }

    /// header with the references in its comment lines replaced by their C spelling.
    pub fn to_c(&self, header: &str) -> String {
        translate(header, "//", &self.c_names)
    }

    /// source with the references in its doc comment lines replaced by their Rust
    /// spelling. Only references to functions whose method is named otherwise change.
    pub fn to_rust(&self, source: &str) -> String {
        translate(source, "///", &self.rust_names)
    }

    /// source with the function references in its comment lines replaced by the C
    /// function the raw bindings declare. Types keep their name there, and an api
    /// block's comment is a plain `//` one.
    pub fn to_sys(&self, source: &str) -> String {
        translate(source, "//", &self.sys_names)
    }

    /// The Rust spelling of the functions in api whose façade method is not named as
    /// the function: a generated `_impl` method, or the `[rust_doc]` name.
    fn add_rust_names(&mut self, api: &Api) {
        for func in RustGen::stateless_methods(api) {
            let method = RustGen::facade_method_name(&func.name);
            if method != func.name {
                self.rust_names.insert(
                    format!("{}::{}", api.name, func.name),
                    format!("{}::{}", api.name, method),
                );
            }
        }
        for func in &api.functions {
            if let Some(rust_name) = &func.rust_doc {
                self.rust_names
                    .insert(format!("{}::{}", api.name, func.name), rust_name.clone());
            }
        }
    }
}

/// text with the references in the lines that start with marker replaced through names.
fn translate(text: &str, marker: &str, names: &HashMap<String, String>) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        if line.trim_start().starts_with(marker) {
            translate_line(line, names, &mut out);
        } else {
            out.push_str(line);
        }
    }
    out
}

fn translate_line(line: &str, names: &HashMap<String, String>, out: &mut String) {
    for (i, (span, quoted)) in spans(line).enumerate() {
        if i > 0 {
            out.push('`');
        }
        let name = call_target(span);
        match names.get(name) {
            Some(new_name) if quoted => {
                out.push_str(new_name);
                out.push_str(&span[name.len()..]);
            }
            _ => out.push_str(span),
        }
    }
}

/// line split at its backticks, each piece with whether a closed pair quotes it.
fn spans(line: &str) -> impl Iterator<Item = (&str, bool)> {
    let last = line.matches('`').count();
    line.split('`')
        .enumerate()
        .map(move |(i, span)| (span, i % 2 == 1 && i < last))
}

/// A reference written as a call, `List::begin()`, names `List::begin`.
fn call_target(span: &str) -> &str {
    span.strip_suffix("()").unwrap_or(span)
}

/// The fields a reference can name: the struct's own, plus the arms of an unnamed
/// union, which C reaches directly off the struct.
fn struct_fields(s: &Struct) -> impl Iterator<Item = &crate::api_parser::Variable> {
    s.variables.iter().flat_map(|var| {
        let arms = match &var.union_variants {
            Some(arms) if var.name.is_empty() => arms.as_slice(),
            _ => &[],
        };
        std::iter::once(var)
            .filter(|var| !var.name.is_empty())
            .chain(arms)
    })
}

/// The owner in an `Owner::member` or `Owner.member` reference, when span is one.
fn member_owner(span: &str) -> Option<&str> {
    let (owner, member) = span.split_once("::").or_else(|| span.split_once('.'))?;
    let is_ident =
        |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    (is_ident(owner) && is_ident(member)).then_some(owner)
}

/// Every doc block in def, labelled with the item it documents.
fn doc_blocks(def: &ApiDef) -> Vec<(String, &Vec<String>)> {
    let mut blocks = Vec::new();
    for s in &def.structs {
        blocks.push((s.name.clone(), &s.doc_comments));
        for var in &s.variables {
            blocks.push((format!("{}.{}", s.name, var.name), &var.doc_comments));
            for arm in var.union_variants.iter().flatten() {
                blocks.push((format!("{}.{}", s.name, arm.name), &arm.doc_comments));
            }
        }
        for func in &s.functions {
            blocks.push((format!("{}::{}", s.name, func.name), &func.doc_comments));
        }
    }
    for e in &def.enums {
        blocks.push((e.name.clone(), &e.doc_comments));
        for entry in &e.entries {
            blocks.push((format!("{}::{}", e.name, entry.name), &entry.doc_comments));
        }
    }
    for api in &def.apis {
        blocks.push((api.name.clone(), &api.doc_comments));
        for func in &api.functions {
            blocks.push((format!("{}::{}", api.name, func.name), &func.doc_comments));
        }
    }
    for cb in &def.callbacks {
        blocks.push((cb.name.clone(), &cb.doc_comments));
    }
    for ext in &def.externs {
        blocks.push((ext.name.clone(), &ext.doc_comments));
    }
    blocks
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api_parser::ApiParser;

    const LIST_DEF: &str = "
        /// The outcome, returned by `List::end`.
        struct ListResult {
            /// See `DropRelationship::Before` and `count`.
            requests: u32,
        }
        enum DropRelationship { Before = 0, After }
        api List {
            /// Starts a list. Read `ListResult.requests`, a `ListResult`.
            begin(count: u32) -> u32
            end() -> ListResult
            show_impl(config: ListConfig)
            raw_impl(count: u32)
        }
        struct ListConfig { gap: f32 }
        struct Backend { poll() -> bool }
        struct Event { union { moved: u32, key: u32 } }";

    fn parse(source: &str) -> Vec<ApiDef> {
        let mut def = ApiDef::default();
        ApiParser::parse_string(source, "list.def", &mut def);
        let mut defs = vec![def];
        ApiParser::second_pass(&mut defs, &crate::naming::FL);
        defs
    }

    fn refs(defs: &[ApiDef]) -> DocRefs {
        DocRefs::new(defs, &crate::naming::FL)
    }

    #[test]
    fn comment_lines_name_the_c_spelling() {
        let defs = parse(LIST_DEF);
        let header = "// Call `List::begin`, read `ListResult.requests` of a `ListResult`.\n\
                      // `DropRelationship::Before`, `List::end()` and `count`.\n\
                      // `List::show_impl`, `List::raw_impl`, `Backend::poll`, `Event.key`.\n";
        assert_eq!(
            refs(&defs).to_c(header),
            "// Call `fl_list_begin`, read `FlListResult.requests` of a `FlListResult`.\n\
             // `FlDropRelationship_Before`, `fl_list_end()` and `count`.\n\
             // `fl_list_show`, `fl_list_raw_impl`, `FlBackend.poll`, `FlEvent.key`.\n"
        );
    }

    #[test]
    fn doc_lines_name_the_rust_spelling() {
        let defs = parse(
            "api Input {
                 [manual] [rust_doc(List::show)] list(count: u32)
                 [rename(text)] get_text() -> u32
                 [manual] [rust_doc(Field::edit)] show_impl()
                 [manual] raw_impl()
                 open_impl(count: u32)
                 hot_id() -> u64
             }",
        );
        let source = "/// See `Input::list`, `Input::get_text()` and `Input::show_impl`.\n\
                      /// `Input::open_impl` is generated, `Input::raw_impl` is not.\n\
                      \x20   /// `Input::hot_id` and Input::list stay.\n\
                      // `Input::list`\n\
                      let s = \"`Input::list`\";\n";
        assert_eq!(
            refs(&defs).to_rust(source),
            "/// See `List::show`, `Input::get_text()` and `Field::edit`.\n\
             /// `Input::open` is generated, `Input::raw_impl` is not.\n\
             \x20   /// `Input::hot_id` and Input::list stay.\n\
             // `Input::list`\n\
             let s = \"`Input::list`\";\n"
        );
    }

    #[test]
    fn only_a_stateless_generated_method_drops_impl() {
        let defs = parse(
            "struct Image { id: u32 }
             api Buffer {
                 [drop] destroy(state: *void)
                 resize_impl(state: *void, count: u32)
             }
             api Loader {
                 [transfer(free = free_impl)] load_impl() -> *Image
                 free_impl(image: *Image)
             }",
        );
        let source = "/// `Buffer::resize_impl`, `Loader::load_impl`, `Loader::free_impl`.\n";
        assert_eq!(
            refs(&defs).to_rust(source),
            "/// `Buffer::resize_impl`, `Loader::load`, `Loader::free_impl`.\n"
        );
    }

    #[test]
    fn raw_binding_docs_name_the_linked_c_function() {
        let defs = parse(LIST_DEF);
        let source = "/// Call `List::begin` or `List::show_impl` with a `ListConfig`.\n\
                      /// It takes a `String`.\n\
                      // Then `List::end`.\n\
                      let s = \"`List::begin`\";\n";
        assert_eq!(
            refs(&defs).to_sys(source),
            "/// Call `fl_list_begin` or `fl_list_show_impl` with a `ListConfig`.\n\
             /// It takes a `String`.\n\
             // Then `fl_list_end`.\n\
             let s = \"`List::begin`\";\n"
        );
        assert_eq!(refs(&defs).to_c("// A `String`.\n"), "// A `FlString`.\n");
    }

    #[test]
    fn code_lines_and_unquoted_names_are_left_alone() {
        let defs = parse(LIST_DEF);
        let header = "FL_API FlListResult fl_list_end(void); // `List::end`\n\
                      // A ListResult, and an unclosed `ListResult\n";
        assert_eq!(refs(&defs).to_c(header), header);
    }

    #[test]
    fn every_reference_in_the_fixture_resolves() {
        let defs = parse(LIST_DEF);
        assert_eq!(refs(&defs).unresolved(&defs[0]), Vec::<String>::new());
    }

    #[test]
    fn a_member_its_owner_lacks_is_reported() {
        let defs = parse(
            "struct ListResult { requests: u32 }
             api List {
                 /// See `List::start()`, `ListResult.count`, `Other::thing` and `a.b`.
                 begin()
             }",
        );
        assert_eq!(
            refs(&defs).unresolved(&defs[0]),
            vec![
                "  List::begin: `List::start()`",
                "  List::begin: `ListResult.count`"
            ]
        );
    }
}
