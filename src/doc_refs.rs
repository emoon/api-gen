//! References between items in doc comments. A `.def` comment names another item by
//! its IDL spelling in backticks; the C header shows the name a C caller writes.

use crate::api_parser::{ApiDef, Enum, Struct};
use crate::naming::Naming;
use std::collections::{HashMap, HashSet};

/// Every item a doc comment can name, with its C spelling.
#[derive(Debug, Default)]
pub struct DocRefs {
    /// IDL reference (`List::begin`, `ListResult`, `ListResult.requests`) to C spelling.
    c_names: HashMap<String, String>,
    /// Names of the types and api blocks, which own the members a reference can name.
    owners: HashSet<String>,
}

impl DocRefs {
    pub fn new(api_defs: &[ApiDef], naming: &Naming) -> DocRefs {
        let mut refs = DocRefs::default();
        for def in api_defs {
            for s in &def.structs {
                refs.add_struct(s, naming);
            }
            for e in &def.enums {
                refs.add_enum(e, naming);
            }
            for api in &def.apis {
                refs.owners.insert(api.name.clone());
                for func in &api.functions {
                    refs.add_func(&api.name, &func.name, &func.c_name);
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

    /// A C caller writes the convenience macro, which drops the `_impl` suffix.
    fn add_func(&mut self, owner: &str, name: &str, c_name: &str) {
        let call_name = c_name.strip_suffix("_impl").unwrap_or(c_name);
        self.c_names
            .insert(format!("{owner}::{name}"), call_name.to_owned());
    }

    fn add_struct(&mut self, s: &Struct, naming: &Naming) {
        let c_type = naming.c_type(&s.name);
        for var in &s.variables {
            self.c_names.insert(
                format!("{}.{}", s.name, var.name),
                format!("{}.{}", c_type, var.name),
            );
        }
        for func in &s.functions {
            self.add_func(&s.name, &func.name, &func.c_name);
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
            for span in comments.iter().flat_map(|line| backtick_spans(line)) {
                if self.is_unresolved(span) {
                    missing.push(format!("  {item}: `{span}`"));
                }
            }
        }
        missing
    }

    fn is_unresolved(&self, span: &str) -> bool {
        match member_owner(span) {
            Some(owner) => self.owners.contains(owner) && !self.c_names.contains_key(span),
            None => false,
        }
    }

    /// header with the references in its comment lines replaced by their C spelling.
    pub fn to_c(&self, header: &str) -> String {
        let mut out = String::with_capacity(header.len());
        for line in header.split_inclusive('\n') {
            if line.trim_start().starts_with("//") {
                out.push_str(&self.line_to_c(line));
            } else {
                out.push_str(line);
            }
        }
        out
    }

    fn line_to_c(&self, line: &str) -> String {
        let mut out = String::with_capacity(line.len());
        for (i, part) in line.split('`').enumerate() {
            if i > 0 {
                out.push('`');
            }
            let in_backticks = i % 2 == 1;
            match self.c_names.get(part) {
                Some(c_name) if in_backticks => out.push_str(c_name),
                _ => out.push_str(part),
            }
        }
        out
    }
}

/// The text between each pair of backticks on a line.
fn backtick_spans(line: &str) -> impl Iterator<Item = &str> {
    let closed = line.matches('`').count() / 2;
    line.split('`').skip(1).step_by(2).take(closed)
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
            new_impl(count: u32)
        }";

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
                      // `DropRelationship::Before`, `List::new_impl` and `count`.\n";
        assert_eq!(
            refs(&defs).to_c(header),
            "// Call `fl_list_begin`, read `FlListResult.requests` of a `FlListResult`.\n\
             // `FlDropRelationship_Before`, `fl_list` and `count`.\n"
        );
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
                 /// See `List::start`, `ListResult.count`, `Other::thing` and `a.b`.
                 begin()
             }",
        );
        assert_eq!(
            refs(&defs).unresolved(&defs[0]),
            vec![
                "  List::begin: `List::start`",
                "  List::begin: `ListResult.count`"
            ]
        );
    }
}
