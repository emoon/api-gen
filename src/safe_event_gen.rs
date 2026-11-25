//! The safe Rust form of a tag-plus-union struct.
//!
//! A struct whose anonymous union is declared `union(<tag field>) { [tag(<Variant>)] arm: T }`
//! says which tag selects which payload. This module turns that into three types in the
//! struct's generated Rust module: a `<Struct>Kind` enum whose variants carry the payload
//! (a tag no arm names becomes a unit variant), a `Safe<Struct>` struct holding that enum
//! and the struct's other fields, and an `Invalid<Struct>` error. `Safe<Struct>` converts
//! into the C struct with `From`, and back with the unsafe `try_from_raw`, which checks the
//! tag and every enum in the live payload before anything is read as a Rust enum.

use crate::api_parser::{ApiDef, Enum, EnumType, Struct, Variable, VariableType};
use crate::layout::type_size_align;
use crate::rust_gen::RustGen;
use heck::ToUpperCamelCase;
use std::collections::BTreeSet;
use std::io::{self, Write};

/// The indexes of a struct's tag field and tagged union field, when it has one.
pub fn tagged_union(sdef: &Struct) -> Option<(usize, usize)> {
    let union_index = sdef
        .variables
        .iter()
        .position(|v| v.union_variants.is_some() && v.union_tag.is_some())?;
    let tag = sdef.variables[union_index].union_tag.as_deref()?;
    let tag_index = sdef.variables.iter().position(|v| v.name == tag)?;
    Some((tag_index, union_index))
}

/// One value of the struct that holds an integer the Rust side must check before it reads
/// the value as an enum or a bool.
struct RawCheck {
    /// How the error names the field: `button`, `type`.
    label: String,
    /// A `usize` expression: the byte offset of the value from the start of the struct.
    offset: String,
    kind: CheckKind,
}

enum CheckKind {
    /// A u32 that must be a value of this enum (spelled as Rust).
    Enum(String),
    /// A byte that must be 0 or 1.
    Bool,
}

/// Everything one tagged struct's emission needs to know.
struct Plan<'a> {
    root: &'a str,
    api_def: &'a ApiDef,
    sdef: &'a Struct,
    tag: &'a Variable,
    tag_enum: &'a Enum,
    union_var: &'a Variable,
    arms: &'a [Variable],
    /// The struct's fields other than the tag and the union.
    plain: Vec<&'a Variable>,
    payload_field: String,
}

impl<'a> Plan<'a> {
    fn name(&self) -> &str {
        &self.sdef.name
    }
    fn kind(&self) -> String {
        format!("{}Kind", self.name())
    }
    fn safe(&self) -> String {
        format!("Safe{}", self.name())
    }
    fn err(&self) -> String {
        format!("Invalid{}", self.name())
    }
    fn tag_ident(&self) -> String {
        RustGen::rust_ident(&self.tag.name)
    }
    fn tag_ty(&self) -> String {
        RustGen::rust_field_type(self.root, self.tag)
    }
    /// The tag enum's variants that exist in Rust, in declaration order, each with the arm
    /// that carries its payload.
    fn variants(
        &self,
    ) -> io::Result<Vec<(&'a crate::api_parser::EnumEntry, Option<&'a Variable>)>> {
        let mut out = Vec::new();
        for entry in &self.tag_enum.entries {
            let literal = self
                .tag_enum
                .entry_value_literal(entry)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            if literal.is_some() {
                let arm = self.arms.iter().find(|a| a.tags.contains(&entry.name));
                out.push((entry, arm));
            }
        }
        Ok(out)
    }
    /// Whether a value is a string, which the safe event borrows as a `&str` and does not carry as
    /// a raw view that safe code could point anywhere.
    fn is_string(var: &Variable) -> bool {
        var.vtype == VariableType::Str && !var.pointer && !var.const_pointer && var.array.is_none()
    }
    /// The type a value has in the safe event.
    fn value_ty(&self, var: &Variable) -> String {
        if Self::is_string(var) {
            "&'a str".to_owned()
        } else {
            RustGen::rust_field_type(self.root, var)
        }
    }
    /// The C-side value of a safe one held in `expr`.
    fn to_c(&self, var: &Variable, expr: &str) -> String {
        if Self::is_string(var) {
            format!("{}::RawStr::borrow({expr})", self.root)
        } else {
            expr.to_owned()
        }
    }
    /// The safe value of a C one held in `expr`. Reads a string, so it needs an unsafe block.
    fn from_c(var: &Variable, expr: &str) -> String {
        if Self::is_string(var) {
            format!("{expr}.as_str()")
        } else {
            expr.to_owned()
        }
    }
    /// The payload struct of an arm that holds a string, whose fields the safe variant spells out.
    fn string_payload(&self, arm: &Variable) -> Option<&'a Struct> {
        if arm.pointer || arm.const_pointer || arm.array.is_some() {
            return None;
        }
        let inner = self
            .api_def
            .structs
            .iter()
            .find(|s| s.name == arm.type_name && !s.is_handle_type)?;
        let holds_string = inner.variables.iter().any(Self::is_string);
        if holds_string {
            for field in &inner.variables {
                if self.holds_string(field) && !Self::is_string(field) {
                    self.unsupported(&arm.name, "a payload with a string inside a nested struct");
                }
            }
        }
        holds_string.then_some(inner)
    }
    /// Whether a value is, or is a struct holding, a string.
    fn holds_string(&self, var: &Variable) -> bool {
        if Self::is_string(var) {
            return true;
        }
        if var.pointer || var.const_pointer || var.array.is_some() {
            return false;
        }
        self.api_def
            .structs
            .iter()
            .find(|s| s.name == var.type_name && !s.is_handle_type)
            .is_some_and(|s| s.variables.iter().any(|v| self.holds_string(v)))
    }
    /// Whether the safe event borrows a string, and so carries a lifetime.
    fn borrows(&self) -> bool {
        self.plain.iter().any(|v| self.holds_string(v))
            || self.arms.iter().any(|arm| self.holds_string(arm))
    }
    /// `<'a>` on the safe types that borrow, nothing on the ones that do not.
    fn lt(&self) -> &'static str {
        if self.borrows() {
            "<'a>"
        } else {
            ""
        }
    }
    fn variant_name(entry_name: &str) -> String {
        entry_name.to_upper_camel_case()
    }
    fn offset_of(ty: &str, field: &Variable) -> String {
        format!(
            "core::mem::offset_of!({}, {})",
            ty,
            RustGen::rust_ident(&field.name)
        )
    }

    /// The checks one value needs: itself when it is an enum or a bool, each of its fields
    /// when it is a struct, nothing for plain data.
    fn checks_for(&self, var: &Variable, label: &str, offset: &str, out: &mut Vec<RawCheck>) {
        if var.pointer || var.const_pointer {
            return;
        }
        let ty = var.type_name.as_str();
        let number_or_string = type_size_align(ty).is_some() && ty != "bool";
        if var.array.is_some() {
            if !number_or_string {
                self.unsupported(label, "an array of something other than numbers");
            }
            return;
        }
        if number_or_string {
            return;
        }
        if ty == "bool" {
            out.push(RawCheck {
                label: label.to_owned(),
                offset: offset.to_owned(),
                kind: CheckKind::Bool,
            });
        } else if let Some(edef) = self.api_def.enums.iter().find(|e| e.name == ty) {
            if edef.enum_type != EnumType::Regular || edef.is_packed {
                self.unsupported(label, "a bitflags or packed enum");
            }
            out.push(RawCheck {
                label: label.to_owned(),
                offset: offset.to_owned(),
                kind: CheckKind::Enum(RustGen::rust_field_type(self.root, var)),
            });
        } else if let Some(inner) = self.api_def.structs.iter().find(|s| s.name == ty) {
            if !inner.is_handle_type {
                self.struct_checks(var, inner, label, offset, out);
            }
        } else {
            self.unsupported(label, "a type defined outside this def");
        }
    }

    /// The checks of each field of a struct held by value.
    fn struct_checks(
        &self,
        var: &Variable,
        inner: &Struct,
        label: &str,
        offset: &str,
        out: &mut Vec<RawCheck>,
    ) {
        let inner_ty = RustGen::rust_field_type(self.root, var);
        for field in &inner.variables {
            if field.union_variants.is_some() {
                self.unsupported(label, "a struct holding a union");
            }
            let at = format!("{offset} + {}", Self::offset_of(&inner_ty, field));
            self.checks_for(field, &format!("{label}.{}", field.name), &at, out);
        }
    }

    fn unsupported(&self, label: &str, what: &str) -> ! {
        panic!(
            "api_gen: {}: `{label}` is {what}, which the safe event conversion cannot check",
            self.name()
        )
    }

    /// The checks of the fields outside the union, which every tag needs.
    fn plain_checks(&self) -> Vec<RawCheck> {
        let mut out = Vec::new();
        let name = self.name();
        for var in &self.plain {
            let at = Self::offset_of(name, var);
            self.checks_for(var, &var.name, &at, &mut out);
        }
        out
    }

    /// The checks of one arm's payload.
    fn arm_checks(&self, arm: &Variable) -> Vec<RawCheck> {
        let mut out = Vec::new();
        let payload_at = format!(
            "core::mem::offset_of!({}, {})",
            self.name(),
            self.payload_field
        );
        self.checks_for(arm, &arm.name, &payload_at, &mut out);
        out
    }
}

fn write_check<W: Write>(f: &mut W, check: &RawCheck, err: &str, indent: &str) -> io::Result<()> {
    let read = match check.kind {
        CheckKind::Enum(_) => "bytes.add(OFFSET).cast::<u32>().read_unaligned()",
        CheckKind::Bool => "u32::from(bytes.add(OFFSET).read())",
    }
    .replace("OFFSET", &check.offset);
    writeln!(
        f,
        "{indent}// SAFETY: the caller's contract makes the struct readable, and the offset is inside it."
    )?;
    writeln!(f, "{indent}let value = unsafe {{ {read} }};")?;
    let invalid = match &check.kind {
        CheckKind::Enum(ty) => format!("{ty}::from_raw(value).is_none()"),
        CheckKind::Bool => "value > 1".to_owned(),
    };
    writeln!(f, "{indent}if {invalid} {{")?;
    writeln!(
        f,
        "{indent}    return Err({err} {{ field: \"{}\", value }});",
        check.label
    )?;
    writeln!(f, "{indent}}}")?;
    Ok(())
}

/// Emit the safe event types of one tagged struct. Returns the enums (spelled as Rust)
/// that the conversion calls `from_raw` on, for [`write_from_raw`].
pub fn generate<W: Write>(
    f: &mut W,
    root: &str,
    api_def: &ApiDef,
    sdef: &Struct,
) -> io::Result<BTreeSet<String>> {
    let Some((tag_index, union_index)) = tagged_union(sdef) else {
        return Ok(BTreeSet::new());
    };
    let union_var = &sdef.variables[union_index];
    let tag = &sdef.variables[tag_index];
    let tag_enum = api_def
        .enums
        .iter()
        .find(|e| e.name == tag.type_name)
        .unwrap_or_else(|| {
            panic!(
                "api_gen: {}: the tag enum `{}` must be defined in the same def as the struct",
                sdef.name, tag.type_name
            )
        });
    assert!(
        tag_enum.entries.iter().all(|e| e.name != SENTINEL),
        "api_gen: {}: the tag enum `{}` has a `{SENTINEL}` variant, which is no tag",
        sdef.name,
        tag_enum.name
    );
    assert!(
        !tag_enum.is_packed,
        "api_gen: {}: the tag enum `{}` is packed",
        sdef.name, tag_enum.name
    );
    let plan = Plan {
        root,
        api_def,
        sdef,
        tag,
        tag_enum,
        union_var,
        arms: union_var.union_variants.as_deref().unwrap_or_default(),
        plain: sdef
            .variables
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != tag_index && *i != union_index)
            .map(|(_, v)| v)
            .collect(),
        payload_field: RustGen::union_field_spelling(&sdef.name, union_var).0,
    };

    for var in &plan.plain {
        if plan.holds_string(var) && !Plan::is_string(var) {
            plan.unsupported(&var.name, "a struct holding a string");
        }
    }
    let variants = plan.variants()?;
    write_kind(f, &plan, &variants)?;
    write_safe_struct(f, &plan)?;
    write_error(f, &plan)?;
    write_into_c(f, &plan, &variants)?;
    write_try_from_raw(f, &plan, &variants)?;

    let mut enums = BTreeSet::new();
    enums.insert(plan.tag_ty());
    let mut checks = plan.plain_checks();
    for arm in plan.arms {
        checks.extend(plan.arm_checks(arm));
    }
    for check in checks {
        if let CheckKind::Enum(ty) = check.kind {
            enums.insert(ty);
        }
    }
    Ok(enums)
}

type Variants<'a> = [(&'a crate::api_parser::EnumEntry, Option<&'a Variable>)];

fn write_kind<W: Write>(f: &mut W, plan: &Plan, variants: &Variants) -> io::Result<()> {
    writeln!(
        f,
        "/// What a [`{name}`] reports, with the payload its `{tag}` selects.",
        name = plan.name(),
        tag = plan.tag.name
    )?;
    writeln!(f, "///")?;
    writeln!(
        f,
        "/// The safe form of the tag and the payload union: a variant holds the payload of its tag, and one without a payload"
    )?;
    writeln!(f, "/// has none to read.")?;
    writeln!(f, "#[derive(Copy, Clone, Debug)]")?;
    writeln!(f, "pub enum {}{} {{", plan.kind(), plan.lt())?;
    for (entry, arm) in variants {
        RustGen::write_comment(f, &entry.doc_comments, 4)?;
        let name = Plan::variant_name(&entry.name);
        match arm {
            Some(arm) => match plan.string_payload(arm) {
                Some(inner) => {
                    writeln!(f, "    {name} {{")?;
                    for field in &inner.variables {
                        writeln!(
                            f,
                            "        {}: {},",
                            RustGen::rust_ident(&field.name),
                            plan.value_ty(field)
                        )?;
                    }
                    writeln!(f, "    }},")?;
                }
                None => writeln!(f, "    {name}({}),", plan.value_ty(arm))?,
            },
            None => writeln!(f, "    {name},")?,
        }
    }
    writeln!(f, "}}")?;
    writeln!(f)
}

fn write_safe_struct<W: Write>(f: &mut W, plan: &Plan) -> io::Result<()> {
    writeln!(
        f,
        "/// A [`{name}`] as safe Rust: its [`{kind}`] and the fields that do not depend on it.",
        name = plan.name(),
        kind = plan.kind()
    )?;
    writeln!(f, "///")?;
    writeln!(
        f,
        "/// `{safe}` converts into a [`{name}`] with `From`, and a [`{name}`] from C converts back with",
        safe = plan.safe(),
        name = plan.name()
    )?;
    writeln!(f, "/// [`{safe}::try_from_raw`].", safe = plan.safe())?;
    writeln!(f, "#[derive(Copy, Clone, Debug)]")?;
    writeln!(f, "pub struct {}{} {{", plan.safe(), plan.lt())?;
    writeln!(f, "    pub kind: {}{},", plan.kind(), plan.lt())?;
    for var in &plan.plain {
        RustGen::write_comment(f, &var.doc_comments, 4)?;
        writeln!(
            f,
            "    pub {}: {},",
            RustGen::rust_ident(&var.name),
            plan.value_ty(var)
        )?;
    }
    writeln!(f, "}}")?;
    writeln!(f)
}

fn write_error<W: Write>(f: &mut W, plan: &Plan) -> io::Result<()> {
    let (err, name) = (plan.err(), plan.name());
    writeln!(
        f,
        "/// Why [`{safe}::try_from_raw`] refused a [`{name}`]: `field` holds `value`, which no variant of its type has.",
        safe = plan.safe()
    )?;
    writeln!(f, "#[derive(Copy, Clone, Debug, PartialEq, Eq)]")?;
    writeln!(f, "pub struct {err} {{")?;
    writeln!(
        f,
        "    /// The field, as the IDL names it. A field of the payload is `arm.field`."
    )?;
    writeln!(f, "    pub field: &'static str,")?;
    writeln!(f, "    /// The value C wrote there.")?;
    writeln!(f, "    pub value: u32,")?;
    writeln!(f, "}}")?;
    writeln!(f)?;
    writeln!(f, "impl core::fmt::Display for {err} {{")?;
    writeln!(
        f,
        "    fn fmt(&self, out: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{"
    )?;
    writeln!(
        f,
        "        write!(out, \"invalid {name}: field `{{}}` holds {{}}\", self.field, self.value)"
    )?;
    writeln!(f, "    }}")?;
    writeln!(f, "}}")?;
    writeln!(f)?;
    writeln!(f, "impl core::error::Error for {err} {{}}")?;
    writeln!(f)
}

fn write_into_c<W: Write>(f: &mut W, plan: &Plan, variants: &Variants) -> io::Result<()> {
    let (name, safe, kind, lt) = (plan.name(), plan.safe(), plan.kind(), plan.lt());
    let tag_ty = plan.tag_ty();
    let payload_ty = RustGen::union_field_spelling(name, plan.union_var).1;
    let impl_lt = if lt.is_empty() { "" } else { "<'a>" };
    writeln!(f, "impl{impl_lt} From<{safe}{lt}> for {name} {{")?;
    writeln!(f, "    fn from(event: {safe}{lt}) -> {name} {{")?;
    writeln!(
        f,
        "        let ({tag}, {payload}) = match event.kind {{",
        tag = plan.tag_ident(),
        payload = plan.payload_field
    )?;
    for (entry, arm) in variants {
        let variant = Plan::variant_name(&entry.name);
        let Some(arm) = arm else {
            writeln!(f, "            {kind}::{variant} => (")?;
            writeln!(f, "                {tag_ty}::{},", entry.name)?;
            writeln!(f, "                // SAFETY: every bit pattern is a valid union value, and no arm is read for this tag.")?;
            writeln!(f, "                unsafe {{ core::mem::zeroed() }},")?;
            writeln!(f, "            ),")?;
            continue;
        };
        let arm_ident = RustGen::rust_ident(&arm.name);
        match plan.string_payload(arm) {
            Some(inner) => {
                let fields: Vec<String> = inner
                    .variables
                    .iter()
                    .map(|v| RustGen::rust_ident(&v.name))
                    .collect();
                let built: Vec<String> = inner
                    .variables
                    .iter()
                    .zip(&fields)
                    .map(|(v, ident)| {
                        let value = plan.to_c(v, ident);
                        if value == *ident {
                            value
                        } else {
                            format!("{ident}: {value}")
                        }
                    })
                    .collect();
                let arm_ty = RustGen::rust_field_type(plan.root, arm);
                writeln!(
                    f,
                    "            {kind}::{variant} {{ {} }} => ({tag_ty}::{entry}, {payload_ty} {{ {arm_ident}: {arm_ty} {{ {} }} }}),",
                    fields.join(", "),
                    built.join(", "),
                    entry = entry.name
                )?;
            }
            None => writeln!(
                f,
                "            {kind}::{variant}(data) => ({tag_ty}::{entry}, {payload_ty} {{ {arm_ident}: {} }}),",
                plan.to_c(arm, "data"),
                entry = entry.name
            )?,
        }
    }
    writeln!(f, "        }};")?;
    writeln!(f, "        {name} {{")?;
    writeln!(f, "            {tag},", tag = plan.tag_ident())?;
    writeln!(f, "            {payload},", payload = plan.payload_field)?;
    for var in &plan.plain {
        let ident = RustGen::rust_ident(&var.name);
        writeln!(
            f,
            "            {ident}: {},",
            plan.to_c(var, &format!("event.{ident}"))
        )?;
    }
    writeln!(f, "        }}")?;
    writeln!(f, "    }}")?;
    writeln!(f, "}}")?;
    writeln!(f)
}

fn write_try_from_raw<W: Write>(f: &mut W, plan: &Plan, variants: &Variants) -> io::Result<()> {
    let (name, safe, kind, err, lt) =
        (plan.name(), plan.safe(), plan.kind(), plan.err(), plan.lt());
    let tag_ty = plan.tag_ty();
    let tag = plan.tag_ident();
    writeln!(f, "impl{lt} {safe}{lt} {{")?;
    writeln!(
        f,
        "    /// Read a [`{name}`] that C wrote as a safe event, or say which field holds a value no variant has."
    )?;
    writeln!(f, "    ///")?;
    writeln!(
        f,
        "    /// The struct is copied once, and the tag and every enum and bool in the payload it selects are checked as"
    )?;
    writeln!(
        f,
        "    /// integers in that copy before any of them is read as its Rust type, so a stray value is an error and not"
    )?;
    writeln!(f, "    /// undefined behavior.")?;
    writeln!(f, "    ///")?;
    writeln!(f, "    /// # Safety")?;
    writeln!(
        f,
        "    /// `raw` must be valid and aligned for reads of a whole [`{name}`], and the payload arm its tag selects must be"
    )?;
    if plan.borrows() {
        writeln!(
            f,
            "    /// set. A string in that arm must stay valid and unmodified for `'a`."
        )?;
    } else {
        writeln!(f, "    /// set.")?;
    }
    writeln!(
        f,
        "    pub unsafe fn try_from_raw(raw: *const {name}) -> Result<{safe}{lt}, {err}> {{"
    )?;
    writeln!(
        f,
        "        let mut copy = core::mem::MaybeUninit::<{name}>::uninit();"
    )?;
    writeln!(f, "        // SAFETY: the caller's contract makes raw readable for a whole struct, and copy is that large and apart from it.")?;
    writeln!(f, "        unsafe {{")?;
    writeln!(
        f,
        "            core::ptr::copy_nonoverlapping(raw.cast::<u8>(), copy.as_mut_ptr().cast::<u8>(), core::mem::size_of::<{name}>());"
    )?;
    writeln!(f, "        }}")?;
    writeln!(f, "        let bytes = copy.as_ptr().cast::<u8>();")?;
    writeln!(f, "        // SAFETY: the offset is inside the copy, whose tag the caller's contract has set.")?;
    writeln!(
        f,
        "        let raw_tag = unsafe {{ bytes.add(core::mem::offset_of!({name}, {tag})).cast::<u32>().read_unaligned() }};"
    )?;
    writeln!(
        f,
        "        let tag = {tag_ty}::from_raw(raw_tag).ok_or({err} {{ field: \"{}\", value: raw_tag }})?;",
        plan.tag.name
    )?;
    for check in plan.plain_checks() {
        write_check(f, &check, &err, "        ")?;
    }
    let guarded: Vec<_> = variants
        .iter()
        .filter_map(|(entry, arm)| {
            let checks = plan.arm_checks((*arm)?);
            (!checks.is_empty()).then_some((entry, checks))
        })
        .collect();
    if !guarded.is_empty() {
        writeln!(f, "        match tag {{")?;
        for (entry, checks) in &guarded {
            writeln!(f, "            {tag_ty}::{} => {{", entry.name)?;
            for check in checks {
                write_check(f, check, &err, "                ")?;
            }
            writeln!(f, "            }}")?;
        }
        if guarded.len() < variants.len() {
            writeln!(f, "            _ => {{}}")?;
        }
        writeln!(f, "        }}")?;
    }
    writeln!(f, "        // SAFETY: the copy is a whole struct, and the tag and every enum and bool the read below")?;
    writeln!(
        f,
        "        // touches were checked above; the rest is plain data."
    )?;
    writeln!(f, "        let event = unsafe {{ copy.assume_init() }};")?;
    writeln!(f, "        // SAFETY: the tag selects the payload arm that C set and that arm was checked above, and the")?;
    writeln!(
        f,
        "        // caller's contract keeps any string in it valid for the result."
    )?;
    writeln!(f, "        let safe = unsafe {{")?;
    writeln!(f, "            {safe} {{")?;
    writeln!(f, "                kind: match tag {{")?;
    for (entry, arm) in variants {
        let variant = Plan::variant_name(&entry.name);
        let value = match arm {
            None => format!("{kind}::{variant}"),
            Some(arm) => {
                let at = format!(
                    "event.{}.{}",
                    plan.payload_field,
                    RustGen::rust_ident(&arm.name)
                );
                match plan.string_payload(arm) {
                    Some(inner) => {
                        let fields: Vec<String> = inner
                            .variables
                            .iter()
                            .map(|v| {
                                let ident = RustGen::rust_ident(&v.name);
                                format!("{ident}: {}", Plan::from_c(v, &format!("{at}.{ident}")))
                            })
                            .collect();
                        format!("{kind}::{variant} {{ {} }}", fields.join(", "))
                    }
                    None => format!("{kind}::{variant}({})", Plan::from_c(arm, &at)),
                }
            }
        };
        writeln!(
            f,
            "                    {tag_ty}::{} => {value},",
            entry.name
        )?;
    }
    writeln!(f, "                }},")?;
    for var in &plan.plain {
        let ident = RustGen::rust_ident(&var.name);
        writeln!(
            f,
            "                {ident}: {},",
            Plan::from_c(var, &format!("event.{ident}"))
        )?;
    }
    writeln!(f, "            }}")?;
    writeln!(f, "        }};")?;
    writeln!(f, "        Ok(safe)")?;
    writeln!(f, "    }}")?;
    writeln!(f, "}}")?;
    writeln!(f)
}

/// The variant name that marks the number of variants, which no value of the enum has.
const SENTINEL: &str = "Count";

/// Emit `from_raw` for each enum a tagged struct's conversion checks. A variant named
/// `Count` is the size of the enum and not one of its values, so `from_raw` refuses it.
pub fn write_from_raw<W: Write>(
    f: &mut W,
    api_def: &ApiDef,
    enums: &BTreeSet<String>,
) -> io::Result<()> {
    for ty in enums {
        let bare = ty.rsplit("::").next().unwrap_or(ty);
        let edef = api_def
            .enums
            .iter()
            .find(|e| e.name == bare)
            .unwrap_or_else(|| unreachable!("a checked enum is defined in this def"));
        writeln!(f, "const _: () = assert!(core::mem::size_of::<{bare}>() == 4, \"{bare} is read as a u32\");")?;
        writeln!(f)?;
        writeln!(f, "impl {bare} {{")?;
        writeln!(
            f,
            "    /// The variant whose value is `raw`, or [`None`] when no variant has it: what an integer from C must pass"
        )?;
        writeln!(f, "    /// before it is a [`{bare}`].")?;
        let mut values = Vec::new();
        for entry in &edef.entries {
            let has_value = edef
                .entry_value_literal(entry)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
                .is_some();
            if has_value && entry.name != SENTINEL {
                values.push(format!("{bare}::{}", entry.name));
            }
        }
        writeln!(f, "    pub fn from_raw(raw: u32) -> Option<{bare}> {{")?;
        writeln!(
            f,
            "        const VALUES: [{bare}; {}] = [{}];",
            values.len(),
            values.join(", ")
        )?;
        writeln!(
            f,
            "        VALUES.into_iter().find(|value| *value as u32 == raw)"
        )?;
        writeln!(f, "    }}")?;
        writeln!(f, "}}")?;
        writeln!(f)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::rust_gen::tests::{find_rustc, parse_one, strip_file_header};
    use std::process::Command;

    const PTR_DEF: &str = "\
enum PtrType { Move = 0, Down, Up, Enter, Hover, Dropped = 9, }
enum Button { Left = 0, Right, Count }
enum Mode { Slow = 2, Fast = 7, }
#[attributes(Copy)]
struct MoveData { x: f32, y: f32 }
#[attributes(Copy)]
struct Inner { button: Button, pressed: bool }
#[attributes(Copy)]
struct ButtonData { inner: Inner, x: f32 }
#[attributes(Copy)]
struct DropData { path: String, x: f32 }
#[attributes(Copy)]
struct PtrEvent {
    type: PtrType,
    id: u32,
    mode: Mode,
    label: String,
    union(type) {
        [tag(Move)] move: MoveData,
        [tag(Down, Up)] button: ButtonData,
        [tag(Hover)] hover: Button,
        [tag(Dropped)] dropped: DropData
    },
    stamp: u64,
}
";

    /// The one piece of the flowi crate the generated module names that the test does not define:
    /// a string view with the `borrow` and `as_str` the conversions call.
    const RAW_STR_STUB: &str = "
#[derive(Copy, Clone, Debug)]
pub struct RawStr { data: *const u8, len: usize }
impl RawStr {
    pub fn borrow(s: &str) -> RawStr { RawStr { data: s.as_ptr(), len: s.len() } }
    pub unsafe fn as_str<'a>(&self) -> &'a str {
        unsafe { core::str::from_utf8_unchecked(core::slice::from_raw_parts(self.data, self.len)) }
    }
}
";

    /// The def's generated module, as the generator writes it.
    fn generated(defs: &str) -> String {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let unique = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let api_def = parse_one(defs, "ptr.def");
        let reg = crate::layout::TypeRegistry::build(std::slice::from_ref(&api_def));
        let dir = std::env::temp_dir().join(format!(
            "api_gen_safe_event_{}_{unique}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).expect("mk dir");
        crate::rust_gen::RustGen::generate(
            dir.to_str().expect("utf8 path"),
            &api_def,
            &reg,
            "scripts/gen.sh",
            "crate",
            &crate::doc_refs::DocRefs::default(),
        )
        .expect("generate");
        let out = std::fs::read_to_string(dir.join("ptr.rs")).expect("read generated");
        let _ = std::fs::remove_dir_all(&dir);
        out
    }

    /// Compile the generated module with a main, run it, and return whether it exited cleanly.
    fn runs(rustc: &str, tag: &str, module: &str, main: &str) -> bool {
        let dir =
            std::env::temp_dir().join(format!("api_gen_safe_run_{}_{tag}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let src = dir.join("main.rs");
        let exe = dir.join("main");
        std::fs::write(
            &src,
            format!(
                "{}\n{RAW_STR_STUB}\nfn main() {{\n{main}\n}}\n",
                strip_file_header(module)
            ),
        )
        .expect("write source");
        let compiled = Command::new(rustc)
            .args(["--edition=2021", "-o"])
            .arg(&exe)
            .arg(&src)
            .output()
            .expect("run rustc");
        assert!(
            compiled.status.success(),
            "generated module must compile: {}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let ran = Command::new(&exe).output().expect("run generated program");
        let ok = ran.status.success();
        if !ok {
            eprintln!("{}", String::from_utf8_lossy(&ran.stderr));
        }
        let _ = std::fs::remove_dir_all(&dir);
        ok
    }

    #[test]
    fn a_tagged_union_emits_the_safe_enum_the_struct_and_both_conversions() {
        let out = generated(PTR_DEF);
        for expected in [
            "pub enum PtrEventKind<'a> {",
            "    Move(crate::MoveData),",
            "    Down(crate::ButtonData),",
            "    Up(crate::ButtonData),",
            "    Enter,",
            "    Hover(crate::Button),",
            "    Dropped {\n        path: &'a str,\n        x: f32,\n    },",
            "pub struct SafePtrEvent<'a> {",
            "    pub kind: PtrEventKind<'a>,",
            "    pub label: &'a str,",
            "impl<'a> From<SafePtrEvent<'a>> for PtrEvent {",
            "pub unsafe fn try_from_raw(raw: *const PtrEvent) -> Result<SafePtrEvent<'a>, InvalidPtrEvent> {",
            "valid and aligned",
            "impl PtrType {",
            "impl Button {",
            "impl Mode {",
            "size_of::<Mode>() == 4",
        ] {
            assert!(out.contains(expected), "missing `{expected}` in:\n{out}");
        }
        assert!(
            !out.contains("impl MoveData") && !out.contains("impl SafeMoveData"),
            "only the tagged struct gets safe types: {out}"
        );
        assert_eq!(
            out.matches("copy_nonoverlapping").count(),
            1,
            "the struct is read once"
        );
        assert!(
            !out.contains("raw.read()"),
            "the checked bytes are the ones converted: {out}"
        );
    }

    #[test]
    fn a_struct_without_strings_has_no_lifetime() {
        let out = generated(
            "enum T { A = 0, B, }\n#[attributes(Copy)]\nstruct D { x: f32 }\n\
             #[attributes(Copy)]\nstruct E { t: T, union(t) { [tag(A)] d: D }, stamp: u64 }",
        );
        assert!(out.contains("pub enum EKind {"), "no lifetime: {out}");
        assert!(out.contains("pub struct SafeE {"), "no lifetime: {out}");
        assert!(!out.contains("'a"), "no lifetime anywhere: {out}");
    }

    #[test]
    fn a_struct_without_a_tagged_union_gets_no_safe_types() {
        let out = generated(
            "#[attributes(Copy)]\nstruct Plain { x: f32 }\n\
             #[attributes(Copy)]\nstruct Loose { kind: u32, union { a: f32, b: u32 } }",
        );
        assert!(!out.contains("Safe"), "no safe types: {out}");
        assert!(!out.contains("from_raw"), "no from_raw: {out}");
    }

    #[test]
    fn the_safe_enum_round_trips_and_a_stray_value_is_an_error_not_undefined_behavior() {
        let Some(rustc) = find_rustc() else {
            eprintln!("safe event run test skipped: no rustc on PATH");
            return;
        };
        let main = r#"
    fn same(a: &SafePtrEvent, b: &SafePtrEvent) -> bool {
        let kind = match (a.kind, b.kind) {
            (PtrEventKind::Move(x), PtrEventKind::Move(y)) => x.x == y.x && x.y == y.y,
            (PtrEventKind::Down(x), PtrEventKind::Down(y))
            | (PtrEventKind::Up(x), PtrEventKind::Up(y)) => {
                x.inner.button == y.inner.button && x.inner.pressed == y.inner.pressed && x.x == y.x
            }
            (PtrEventKind::Enter, PtrEventKind::Enter) => true,
            (PtrEventKind::Hover(x), PtrEventKind::Hover(y)) => x == y,
            (PtrEventKind::Dropped { path: p, x }, PtrEventKind::Dropped { path: q, x: y }) => {
                p == q && x == y
            }
            _ => false,
        };
        kind && a.id == b.id && a.mode as u32 == b.mode as u32 && a.label == b.label && a.stamp == b.stamp
    }
    let button = ButtonData { inner: Inner { button: Button::Right, pressed: true }, x: 5.0 };
    let events = [
        PtrEventKind::Move(MoveData { x: 1.0, y: 2.0 }),
        PtrEventKind::Down(button),
        PtrEventKind::Up(button),
        PtrEventKind::Enter,
        PtrEventKind::Hover(Button::Right),
        PtrEventKind::Dropped { path: "a/b.wav", x: 9.0 },
    ]
    .map(|kind| SafePtrEvent { kind, id: 3, mode: Mode::Fast, label: "pad", stamp: 4 });

    // Every variant survives the trip, field by field.
    for event in events {
        let c = PtrEvent::from(event);
        // SAFETY: c is a whole, initialised PtrEvent, and the strings are 'static.
        let back = unsafe { SafePtrEvent::try_from_raw(&c) }.expect("a valid event converts back");
        assert!(same(&back, &event), "{back:?} is not {event:?}");
    }
    let down = events[1];
    let moved = events[0];

    // A tag no variant has, in the gap between the non-contiguous values 4 and 9, and past them.
    for stray in [5, 8, 10, 99] {
        let mut c = PtrEvent::from(moved);
        // SAFETY: the tag is the first 4 bytes of c, and the integer is only read back as an integer.
        unsafe { (&mut c as *mut PtrEvent).cast::<u32>().write(stray) };
        // SAFETY: c is a whole PtrEvent; the conversion checks the tag before it reads it.
        let err = unsafe { SafePtrEvent::try_from_raw(&c) }.expect_err("the tag is refused");
        assert_eq!(err, InvalidPtrEvent { field: "type", value: stray });
    }
    assert_eq!(err_text(), "invalid PtrEvent: field `type` holds 99");
    fn err_text() -> String {
        InvalidPtrEvent { field: "type", value: 99 }.to_string()
    }

    // An enum in a plain field: Mode has the values 2 and 7 only.
    for stray in [0, 3, 8] {
        let mut c = PtrEvent::from(moved);
        poke(&mut c, core::mem::offset_of!(PtrEvent, mode), stray);
        // SAFETY: c is a whole PtrEvent; the conversion checks the mode before it reads it.
        let err = unsafe { SafePtrEvent::try_from_raw(&c) }.expect_err("the mode is refused");
        assert_eq!(err, InvalidPtrEvent { field: "mode", value: stray });
    }

    // Enums and bools inside a nested struct of the selected arm, and Count, which is no button.
    let inner_at = core::mem::offset_of!(PtrEvent, payload) + core::mem::offset_of!(ButtonData, inner);
    let button_at = inner_at + core::mem::offset_of!(Inner, button);
    let pressed_at = inner_at + core::mem::offset_of!(Inner, pressed);
    for stray in [Button::Count as u32, 7] {
        for tag_event in [events[1], events[2]] {
            let mut c = PtrEvent::from(tag_event);
            poke(&mut c, button_at, stray);
            // SAFETY: c is a whole PtrEvent; the conversion checks the button before it reads it.
            let err = unsafe { SafePtrEvent::try_from_raw(&c) }.expect_err("the button is refused");
            assert_eq!(err, InvalidPtrEvent { field: "button.inner.button", value: stray });
        }
    }
    let mut c = PtrEvent::from(down);
    // SAFETY: pressed is a byte of the payload, written as an integer.
    unsafe { (&mut c as *mut PtrEvent).cast::<u8>().add(pressed_at).write(2) };
    // SAFETY: c is a whole PtrEvent; the conversion checks the byte before it reads a bool.
    let err = unsafe { SafePtrEvent::try_from_raw(&c) }.expect_err("pressed 2 is refused");
    assert_eq!(err, InvalidPtrEvent { field: "button.inner.pressed", value: 2 });

    // An arm that is itself an enum.
    let mut c = PtrEvent::from(events[4]);
    poke(&mut c, core::mem::offset_of!(PtrEvent, payload), 7);
    // SAFETY: c is a whole PtrEvent; the conversion checks the arm before it reads it.
    let err = unsafe { SafePtrEvent::try_from_raw(&c) }.expect_err("the hover button is refused");
    assert_eq!(err, InvalidPtrEvent { field: "hover", value: 7 });

    // Invalid data in an arm the tag does not select is not looked at: every word of the payload
    // is a value no enum has and a bool no byte is, under a tag that selects a plain arm or none.
    let words = core::mem::size_of::<PtrEventPayload>() / 4;
    for event in [moved, events[3]] {
        let mut c = PtrEvent::from(event);
        for word in 0..words {
            poke(&mut c, core::mem::offset_of!(PtrEvent, payload) + word * 4, 0x0707_0707);
        }
        // SAFETY: c is a whole PtrEvent whose payload bytes are plain numbers under these tags.
        let back = unsafe { SafePtrEvent::try_from_raw(&c) }.expect("an unselected arm is not read");
        assert_eq!(core::mem::discriminant(&back.kind), core::mem::discriminant(&event.kind));
    }

    // from_raw takes the declared values and nothing else, Count and the gaps included.
    assert!(matches!(PtrType::from_raw(9), Some(PtrType::Dropped)));
    assert!(matches!(PtrType::from_raw(4), Some(PtrType::Hover)));
    for stray in 5..9 {
        assert!(PtrType::from_raw(stray).is_none());
    }
    assert!(matches!(Mode::from_raw(7), Some(Mode::Fast)));
    assert!(Mode::from_raw(0).is_none());
    assert!(matches!(Button::from_raw(1), Some(Button::Right)));
    assert!(Button::from_raw(Button::Count as u32).is_none());
    assert!(Button::from_raw(u32::MAX).is_none());

    /// Write an integer over the bytes at offset of a C struct.
    fn poke<T>(event: &mut T, offset: usize, value: u32) {
        // SAFETY: every caller passes the offset of a 4-byte field inside the struct.
        unsafe { (event as *mut T).cast::<u8>().add(offset).cast::<u32>().write_unaligned(value) };
    }
"#;
        assert!(
            runs(rustc, "round_trip", &generated(PTR_DEF), main),
            "the generated conversions must round trip and refuse stray values"
        );
    }

    fn rejects(defs: &str) {
        let _ = parse_one(defs, "bad.def");
    }

    #[test]
    #[should_panic(expected = "has `[tag(...)]` but the union has no tag field")]
    fn an_arm_tag_on_an_untagged_union_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: T, union { [tag(A)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "is not a field before the union")]
    fn a_tag_field_that_is_not_a_sibling_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { union(t) { [tag(A)] a: u32 }, t: T }");
    }

    #[test]
    #[should_panic(expected = "must be a plain enum")]
    fn a_tag_field_that_is_not_an_enum_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: u32, union(t) { [tag(A)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "is not a variant of `T`")]
    fn an_arm_tag_that_is_not_a_variant_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: T, union(t) { [tag(B)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "is the tag of two arms")]
    fn a_variant_claimed_by_two_arms_is_refused() {
        rejects(
            "enum T { A = 0, }\nstruct S { t: T, union(t) { [tag(A)] a: u32, [tag(A)] b: u32 } }",
        );
    }

    #[test]
    #[should_panic(expected = "has no `[tag(...)]`")]
    fn an_arm_without_a_tag_in_a_tagged_union_is_refused() {
        rejects("enum T { A = 0, B, }\nstruct S { t: T, union(t) { [tag(A)] a: u32, b: u32 } }");
    }

    #[test]
    #[should_panic(expected = "must be anonymous")]
    fn a_named_tagged_union_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: T, p: union(t) { [tag(A)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "has no other union, but this one has 2")]
    fn a_second_tagged_union_is_refused() {
        rejects(
            "enum T { A = 0, }\nstruct S { t: T, union(t) { [tag(A)] a: u32 }, u: union(t) { [tag(A)] b: u32 } }",
        );
    }

    #[test]
    #[should_panic(expected = "has no other union, but this one has 2")]
    fn an_untagged_union_beside_a_tagged_one_is_refused() {
        rejects(
            "enum T { A = 0, }\nstruct S { t: T, union(t) { [tag(A)] a: u32 }, u: union { b: u32 } }",
        );
    }

    #[test]
    #[should_panic(expected = "cannot be named `kind`")]
    fn a_plain_field_named_kind_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: T, kind: u32, union(t) { [tag(A)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "cannot be named `payload`")]
    fn a_plain_field_named_payload_is_refused() {
        rejects("enum T { A = 0, }\nstruct S { t: T, payload: u32, union(t) { [tag(A)] a: u32 } }");
    }

    #[test]
    #[should_panic(expected = "must be defined in the same def as the struct")]
    fn a_tag_enum_from_another_def_is_refused() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut defs = [ApiDef::default(), ApiDef::default()];
        ApiParser::parse_string("enum T { A = 0, }", "tags.def", &mut defs[0]);
        ApiParser::parse_string(
            "struct S { t: T, union(t) { [tag(A)] a: u32 } }",
            "event.def",
            &mut defs[1],
        );
        ApiParser::second_pass(&mut defs, &crate::naming::FL);
    }

    #[test]
    #[should_panic(expected = "has a `Count` variant, which is no tag")]
    fn a_tag_enum_with_a_count_variant_is_refused() {
        generated(
            "enum T { A = 0, Count }\n#[attributes(Copy)]\nstruct S { t: T, union(t) { [tag(A)] a: u32 } }",
        );
    }

    #[test]
    #[should_panic(expected = "an array of something other than numbers")]
    fn an_arm_holding_an_array_of_structs_is_refused() {
        generated(
            "enum T { A = 0, }\n#[attributes(Copy)]\nstruct I { x: u32 }\n\
             #[attributes(Copy)]\nstruct P { items: [I; 2] }\n\
             #[attributes(Copy)]\nstruct S { t: T, union(t) { [tag(A)] a: P } }",
        );
    }

    #[test]
    #[should_panic(expected = "a bitflags or packed enum")]
    fn an_arm_holding_a_packed_enum_is_refused() {
        generated(
            "enum T { A = 0, }\n#[attributes(packed)]\nenum Small { X = 0, }\n\
             #[attributes(Copy)]\nstruct P { s: Small }\n\
             #[attributes(Copy)]\nstruct S { t: T, union(t) { [tag(A)] a: P } }",
        );
    }

    #[test]
    #[should_panic(expected = "a type defined outside this def")]
    fn an_arm_of_a_type_from_another_def_is_refused() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut defs = [ApiDef::default(), ApiDef::default()];
        ApiParser::parse_string(
            "#[attributes(Copy)]\nstruct Elsewhere { x: u32 }",
            "shared.def",
            &mut defs[0],
        );
        ApiParser::parse_string(
            "enum T { A = 0, }\n#[attributes(Copy)]\nstruct S { t: T, union(t) { [tag(A)] a: Elsewhere } }",
            "event.def",
            &mut defs[1],
        );
        ApiParser::second_pass(&mut defs, &crate::naming::FL);
        let reg = crate::layout::TypeRegistry::build(&defs);
        let dir = std::env::temp_dir().join(format!("api_gen_safe_other_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let _ = crate::rust_gen::RustGen::generate(
            dir.to_str().expect("utf8 path"),
            &defs[1],
            &reg,
            "scripts/gen.sh",
            "crate",
            &crate::doc_refs::DocRefs::default(),
        );
    }
}
