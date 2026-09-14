// LP64 natural-alignment layout computation.
//
// The model is the System V AMD64 / AArch64 LP64 ABI: each scalar has alignment
// equal to its size; a struct's alignment is the max of its fields'; a field is
// placed at the next offset that satisfies its alignment; the struct's size is
// the final offset rounded up to the struct alignment.
//
// Bitfields are not modelled (the only one, FlString's trailing word, stays an
// extern {16, 8} type).

use crate::api_parser::{ApiDef, ArrayType, FieldRef, Struct, Variable, VariableType};
use std::collections::HashMap;

/// {size, align} in bytes for a scalar or extern type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SizeAlign {
    pub size: u64,
    pub align: u64,
}

impl SizeAlign {
    const fn new(size: u64, align: u64) -> Self {
        SizeAlign { size, align }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldLayout {
    pub name: String,
    pub offset: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLayout {
    pub fields: Vec<FieldLayout>,
    pub size: u64,
    pub align: u64,
}

/// {size, align} for an IDL type name.
///
/// The string keyword (FlString) is opaque-for-layout: its trailing bitfield
/// word is never introspected - it is declared {16, 8} and the C guard validates
/// the real FlString against that.
pub fn type_size_align(type_name: &str) -> Option<SizeAlign> {
    let sa = match type_name {
        "i8" | "u8" | "bool" | "char" => SizeAlign::new(1, 1),
        "i16" | "u16" => SizeAlign::new(2, 2),
        "i32" | "u32" | "f32" => SizeAlign::new(4, 4),
        "i64" | "u64" | "f64" => SizeAlign::new(8, 8),
        // LP64: size_t / ptrdiff_t are pointer-width.
        "usize" | "isize" => SizeAlign::new(8, 8),
        // String fields are FlString; the C side checks the real type.
        "String" | "FlString" => SizeAlign::new(16, 8),
        _ => return None,
    };
    Some(sa)
}

/// Per-type info the registry caches: its {size, align} and whether it
/// (transitively) contains an anonymous union - the latter drives Debug
/// derivation, since a union field is not Debug.
struct TypeInfo {
    sa: SizeAlign,
    contains_union: bool,
}

/// Sizes every generated struct/enum across all defs once, so the generators
/// read identical layout constants for nested and union-bearing types.
pub struct TypeRegistry {
    /// Keyed by IDL type name (e.g. LayoutSizing, Color, LayoutDirection).
    info: HashMap<String, TypeInfo>,
}

impl TypeRegistry {
    /// Build the registry from every parsed def. Handle and opaque structs have no
    /// by-value layout and are skipped.
    pub fn build(api_defs: &[ApiDef]) -> TypeRegistry {
        let mut info: HashMap<String, TypeInfo> = HashMap::new();

        // A packed C enum is 1/1; a plain C enum is int-sized (4/4).
        for def in api_defs {
            for e in &def.enums {
                let sa = if e.is_packed {
                    SizeAlign::new(1, 1)
                } else {
                    SizeAlign::new(4, 4)
                };
                info.insert(
                    e.name.clone(),
                    TypeInfo {
                        sa,
                        contains_union: false,
                    },
                );
            }
            // A `callback <Name>` type used as a struct field is a single C function
            // pointer - always {8, 8} on LP64.
            for cb in &def.callbacks {
                info.insert(
                    cb.name.clone(),
                    TypeInfo {
                        sa: SizeAlign::new(8, 8),
                        contains_union: false,
                    },
                );
            }
            // A handle is an integer typedef with no field layout of its own, but a
            // struct can embed it by value - seed its underlying integer width so
            // such a struct resolves.
            for s in &def.structs {
                if let Some(spec) = &s.handle {
                    if let Some(sa) = type_size_align(&spec.int_type) {
                        info.insert(
                            s.name.clone(),
                            TypeInfo {
                                sa,
                                contains_union: false,
                            },
                        );
                    }
                }
            }
        }

        let mut pending: Vec<&Struct> = api_defs
            .iter()
            .flat_map(|d| d.structs.iter())
            .filter(|s| s.is_real_type() && !s.is_handle_type && !s.is_opaque())
            .collect();

        while !pending.is_empty() {
            let mut progressed = false;
            let mut still = Vec::new();
            for s in pending {
                match Self::try_resolve_struct(s, &info) {
                    Some((sa, contains_union)) => {
                        info.insert(s.name.clone(), TypeInfo { sa, contains_union });
                        progressed = true;
                    }
                    None => still.push(s),
                }
            }
            if !progressed {
                let names: Vec<&str> = still.iter().map(|s| s.name.as_str()).collect();
                panic!(
                    "api_gen layout: unresolvable types (cycle or unknown field type): {:?}",
                    names
                );
            }
            pending = still;
        }

        TypeRegistry { info }
    }

    /// Some((size/align, contains_union)) if every field of sdef resolves;
    /// None if a named dependency is not yet in info.
    fn try_resolve_struct(
        sdef: &Struct,
        info: &HashMap<String, TypeInfo>,
    ) -> Option<(SizeAlign, bool)> {
        let mut fields = Vec::with_capacity(sdef.variables.len() + sdef.functions.len());
        let mut contains_union = false;
        // Value + function fields in authored order: a vtable may place a value field
        // after its function-pointers, and the layout must match. A function-field is
        // a C function pointer - always {8, 8} on LP64.
        for field in sdef.ordered_fields() {
            match field {
                FieldRef::Var(i) => {
                    let v = &sdef.variables[i];
                    let (sa, has_union) = Self::resolve_field(v, info)?;
                    contains_union |= has_union;
                    fields.push((v.name.clone(), sa));
                }
                FieldRef::Func(i) => {
                    fields.push((sdef.functions[i].name.clone(), SizeAlign::new(8, 8)));
                }
            }
        }
        let layout = compute_layout(&fields);
        Some((SizeAlign::new(layout.size, layout.align), contains_union))
    }

    /// {size, align} of one field plus whether it is/contains a union. None
    /// if a named dependency is unresolved.
    fn resolve_field(
        var: &Variable,
        info: &HashMap<String, TypeInfo>,
    ) -> Option<(SizeAlign, bool)> {
        if let Some(variants) = &var.union_variants {
            return Some((Self::union_layout(variants, info)?, true));
        }
        Self::resolve_scalar_or_named(var, info)
    }

    /// {size, align} for a non-union field plus its contains_union flag.
    fn resolve_scalar_or_named(
        var: &Variable,
        info: &HashMap<String, TypeInfo>,
    ) -> Option<(SizeAlign, bool)> {
        // The field's element {size, align} ignoring array-ness. A pointer field is
        // pointer-width whatever the pointee, so a self/forward struct pointer never
        // needs the pointee sized.
        let (elem, has_union) = if var.pointer || var.const_pointer {
            (SizeAlign::new(8, 8), false)
        } else {
            match var.vtype {
                VariableType::Str => (SizeAlign::new(16, 8), false),
                VariableType::Primitive => (type_size_align(&var.type_name)?, false),
                _ => {
                    let ti = info.get(&var.type_name)?;
                    (ti.sa, ti.contains_union)
                }
            }
        };
        match &var.array {
            None => Some((elem, has_union)),
            // A fixed-size array is `elem * N`, alignment of the element - including an
            // array of pointers, which is `8 * N`. Only numeric-literal sizes parse; a
            // symbolic size stays deferred.
            Some(ArrayType::SizedArray(n)) => {
                let count: u64 = n.parse().ok()?;
                Some((SizeAlign::new(elem.size * count, elem.align), has_union))
            }
            // An unsized array is a pointer+length pair only used in api args, never
            // a by-value struct field - defer rather than guess.
            Some(ArrayType::Unsized) => None,
        }
    }

    /// A union's {size, align}: the max variant size rounded up to the max
    /// variant alignment. None if a variant's named type is unresolved.
    fn union_layout(variants: &[Variable], info: &HashMap<String, TypeInfo>) -> Option<SizeAlign> {
        let mut size = 0u64;
        let mut align = 1u64;
        for variant in variants {
            let (sa, _) = Self::resolve_scalar_or_named(variant, info)?;
            size = size.max(sa.size);
            align = align.max(sa.align);
        }
        Some(SizeAlign::new(align_up(size, align), align))
    }

    /// Full field-offset layout of a data struct, for the generators' layout
    /// assertions. Every dependency is resolved by now, so a None here is a bug.
    pub fn layout_for(&self, sdef: &Struct) -> StructLayout {
        let fields: Vec<(String, SizeAlign)> = sdef
            .ordered_fields()
            .into_iter()
            .map(|field| match field {
                FieldRef::Var(i) => {
                    let v = &sdef.variables[i];
                    let (sa, _) = Self::resolve_field(v, &self.info).unwrap_or_else(|| {
                        panic!(
                            "api_gen layout: field {} of {} unresolved",
                            v.name, sdef.name
                        )
                    });
                    (v.name.clone(), sa)
                }
                FieldRef::Func(i) => (sdef.functions[i].name.clone(), SizeAlign::new(8, 8)),
            })
            .collect();
        compute_layout(&fields)
    }

    /// A union field's own {size, align}, for the union's layout assertion.
    pub fn union_size_align(&self, variants: &[Variable]) -> SizeAlign {
        Self::union_layout(variants, &self.info)
            .unwrap_or_else(|| panic!("api_gen layout: unresolved union variant"))
    }

    /// Whether a type (by IDL name) transitively contains an anonymous union -
    /// such a struct cannot derive Debug.
    pub fn contains_union(&self, idl_name: &str) -> bool {
        self.info
            .get(idl_name)
            .map(|ti| ti.contains_union)
            .unwrap_or(false)
    }
}

/// Round value up to the next multiple of align (a power of two).
pub fn align_up(value: u64, align: u64) -> u64 {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

/// Compute the LP64 layout of a struct from its ordered {name, size, align}
/// fields. Field order is the .def order - never reordered.
pub fn compute_layout(fields: &[(String, SizeAlign)]) -> StructLayout {
    let mut offset = 0u64;
    let mut max_align = 1u64;
    let mut placed = Vec::with_capacity(fields.len());

    for (name, sa) in fields {
        offset = align_up(offset, sa.align);
        placed.push(FieldLayout {
            name: name.clone(),
            offset,
        });
        offset += sa.size;
        max_align = max_align.max(sa.align);
    }

    StructLayout {
        fields: placed,
        size: align_up(offset, max_align),
        align: max_align,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(name: &str, size: u64, align: u64) -> (String, SizeAlign) {
        (name.to_owned(), SizeAlign::new(size, align))
    }

    #[test]
    fn color_layout() {
        let l = compute_layout(&[f("r", 1, 1), f("g", 1, 1), f("b", 1, 1), f("a", 1, 1)]);
        assert_eq!(l.size, 4);
        assert_eq!(l.align, 1);
        let offsets: Vec<u64> = l.fields.iter().map(|x| x.offset).collect();
        assert_eq!(offsets, vec![0, 1, 2, 3]);
    }

    #[test]
    fn vec2_layout() {
        let l = compute_layout(&[f("x", 4, 4), f("y", 4, 4)]);
        assert_eq!(l.size, 8);
        assert_eq!(l.align, 4);
        assert_eq!(l.fields[1].offset, 4);
    }

    #[test]
    fn app_settings_layout() {
        let l = compute_layout(&[
            f("window_title", 16, 8),
            f("width", 4, 4),
            f("height", 4, 4),
            f("headless", 1, 1),
        ]);
        let offsets: Vec<u64> = l.fields.iter().map(|x| x.offset).collect();
        assert_eq!(offsets, vec![0, 16, 20, 24]);
        assert_eq!(l.align, 8);
        assert_eq!(l.size, 32); // 24 + 1 byte bool -> round up to align 8
    }

    #[test]
    fn mid_struct_padding() {
        let l = compute_layout(&[f("flag", 1, 1), f("count", 4, 4)]);
        assert_eq!(l.fields[1].offset, 4);
        assert_eq!(l.size, 8);
        assert_eq!(l.align, 4);
    }

    #[test]
    fn type_table_spot_checks() {
        assert_eq!(type_size_align("u8"), Some(SizeAlign::new(1, 1)));
        assert_eq!(type_size_align("f32"), Some(SizeAlign::new(4, 4)));
        assert_eq!(type_size_align("u64"), Some(SizeAlign::new(8, 8)));
        assert_eq!(type_size_align("FlString"), Some(SizeAlign::new(16, 8)));
        assert_eq!(type_size_align("String"), Some(SizeAlign::new(16, 8)));
        assert_eq!(type_size_align("WidgetHandle"), None);
    }

    // Each function-field is a {8, 8} pointer slot in its authored position; a value
    // field after the fn-pointers is NOT hoisted ahead of them, and a handle embedded
    // by value sizes by its underlying integer width.
    #[test]
    fn function_fields_are_pointer_sized_in_authored_order() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "#[handle(u32, invalid = 0xFFFFFFFF)]\n\
             struct ImageHandle {}\n\
             struct Backend {\n\
                 ctx: *void,\n\
                 destroy(ctx: *void),\n\
                 poll(ctx: *void, x: i32) -> bool,\n\
                 icon: ImageHandle,\n\
                 trailing_flag: bool,\n\
             }",
            "backend.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let reg = TypeRegistry::build(std::slice::from_ref(&api_def));
        let backend = api_def
            .structs
            .iter()
            .find(|s| s.name == "Backend")
            .unwrap();
        let l = reg.layout_for(backend);

        let offsets: Vec<(&str, u64)> = l
            .fields
            .iter()
            .map(|f| (f.name.as_str(), f.offset))
            .collect();
        assert_eq!(
            offsets,
            vec![
                ("ctx", 0),
                ("destroy", 8),
                ("poll", 16),
                ("icon", 24),
                ("trailing_flag", 28)
            ]
        );
        assert_eq!(l.size, 32, "3 ptr slots + u32 handle + bool, padded to 8");
        assert_eq!(l.align, 8);
    }

    // A usize struct field is pointer-width (size_t on LP64). A pointer field stays
    // {8, 8} regardless of pointee, so a self/forward struct pointer never needs the
    // pointee resolved (no false "cycle").
    #[test]
    fn usize_field_and_struct_pointer_resolve() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Elem { value: *Val, next: *Elem }\n\
             struct Val { payload: *void, kind: usize }",
            "recur.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let reg = TypeRegistry::build(std::slice::from_ref(&api_def));

        let val = api_def.structs.iter().find(|s| s.name == "Val").unwrap();
        let vl = reg.layout_for(val);
        assert_eq!(vl.size, 16);
        assert_eq!(vl.align, 8);
        assert_eq!(
            vl.fields.iter().map(|f| f.offset).collect::<Vec<_>>(),
            vec![0, 8]
        );

        let elem = api_def.structs.iter().find(|s| s.name == "Elem").unwrap();
        let el = reg.layout_for(elem);
        assert_eq!(el.size, 16);
        assert_eq!(el.align, 8);
    }

    #[test]
    fn fixed_array_field_layout() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Cell { name: [u8; 24], scope_width: u8 }",
            "cell.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let reg = TypeRegistry::build(std::slice::from_ref(&api_def));
        let cell = api_def.structs.iter().find(|s| s.name == "Cell").unwrap();
        let l = reg.layout_for(cell);
        assert_eq!(
            l.fields.iter().map(|f| f.offset).collect::<Vec<_>>(),
            vec![0, 24]
        );
        assert_eq!(l.size, 25);
        assert_eq!(l.align, 1);
    }

    #[test]
    fn pointer_array_field_layout() {
        use crate::api_parser::{ApiDef, ApiParser};
        let mut api_def = ApiDef::default();
        ApiParser::parse_string(
            "struct Table { items: [*const Cell; 4], head: *Cell }\n\
             struct Cell { value: u32 }",
            "table.def",
            &mut api_def,
        );
        ApiParser::second_pass(std::slice::from_mut(&mut api_def), &crate::naming::FL);
        let reg = TypeRegistry::build(std::slice::from_ref(&api_def));
        let table = api_def.structs.iter().find(|s| s.name == "Table").unwrap();
        let l = reg.layout_for(table);

        assert_eq!(
            l.fields.iter().map(|f| f.offset).collect::<Vec<_>>(),
            vec![0, 32],
            "array-of-pointers occupies 8 * 4 = 32 bytes, not 8"
        );
        assert_eq!(l.align, 8);
        assert_eq!(l.size, 40);
        assert_eq!(
            l.size - l.fields[1].offset,
            8,
            "plain pointer stays 8 bytes"
        );

        #[repr(C)]
        struct Table {
            items: [*const u32; 4],
            head: *const u32,
        }
        assert_eq!(l.size as usize, std::mem::size_of::<Table>());
        assert_eq!(l.align as usize, std::mem::align_of::<Table>());
    }

    #[test]
    fn align_up_basics() {
        assert_eq!(align_up(0, 8), 0);
        assert_eq!(align_up(1, 8), 8);
        assert_eq!(align_up(16, 8), 16);
        assert_eq!(align_up(17, 4), 20);
    }
}
