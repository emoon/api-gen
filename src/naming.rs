// Defs are 100% prefix-free - a type is Cursor, a function is set. One
// Naming value is the single place the Em/fl_ (types/functions) spelling
// is decided. The Rust side drops the prefix entirely, so this is consumed only
// by c_gen and the parser's function-name pass.

use heck::ToShoutySnakeCase;
use std::borrow::Cow;

/// The Fl/fl_ (types/functions) pair that drives all generated C names.
///
/// `Default` is empty prefixes, which generates nothing usable: it exists so callers can
/// reach [`Config`](crate::Config)'s struct-update syntax, and every caller sets this.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Naming {
    /// C type prefix (Fl -> FlCursor).
    pub type_prefix: Cow<'static, str>,
    /// C function prefix (fl -> fl_cursor_set).
    pub func_prefix: Cow<'static, str>,
    /// C spelling of the built-in String base type. None derives it from the
    /// type prefix (Fl -> FlString).
    pub string_type: Option<Cow<'static, str>>,
    /// Bracket-include path of the header defining [`Naming::string_type`]
    /// (e.g. flowi/core/string.h). None derives the flowi-layout default,
    /// `<{include-prefix}/core/string.h>`. Set together with string_type.
    pub string_include: Option<Cow<'static, str>>,
}

impl Naming {
    /// Build an owned Naming; the const [`FL`] is the built-in flowi profile.
    pub fn new(type_prefix: &str, func_prefix: &str) -> Naming {
        Naming {
            type_prefix: Cow::Owned(type_prefix.to_owned()),
            func_prefix: Cow::Owned(func_prefix.to_owned()),
            string_type: None,
            string_include: None,
        }
    }

    /// C type spelling of an unprefixed IDL type name (Cursor -> FlCursor).
    pub fn c_type(&self, idl_name: &str) -> String {
        format!("{}{}", self.type_prefix, idl_name)
    }

    /// C spelling of the built-in String base type: the pinned
    /// [`Naming::string_type`] when set, else the prefixed default.
    pub fn c_string_type(&self) -> String {
        match &self.string_type {
            Some(s) => s.to_string(),
            None => self.c_type("String"),
        }
    }

    /// C export-annotation macro carried by every generated public prototype
    /// (Fl -> FL_API, Rp -> RP_API).
    pub fn c_api_macro(&self) -> String {
        format!("{}_API", self.type_prefix.to_shouty_snake_case())
    }

    /// Stem of the header defining [`Naming::c_api_macro`]
    /// (fl -> fl_api.h, rp -> rp_api.h).
    pub fn c_api_header(&self) -> String {
        format!("{}_api.h", self.func_prefix)
    }

    /// C enumerator spelling (CursorShape + Arrow -> FlCursorShape_Arrow).
    pub fn c_enumerator(&self, idl_enum: &str, variant: &str) -> String {
        format!("{}{}_{}", self.type_prefix, idl_enum, variant)
    }

    /// C function spelling (cursor + set -> fl_cursor_set); the receiver is
    /// already snake_cased by the caller.
    pub fn c_func(&self, recv_snake: &str, fn_name: &str) -> String {
        format!("{}_{}_{}", self.func_prefix, recv_snake, fn_name)
    }

    /// C function spelling of an api block slot. A slot spelled new drops the
    /// slot word entirely (Button + new -> fl_button); new_impl keeps only
    /// the _impl suffix (fl_button_impl), which c_gen's strip-to-macro
    /// mechanism then turns into the bare fl_button convenience macro. Every
    /// other slot is the all-suffixed [`c_func`] spelling.
    pub fn c_api_func(&self, api_snake: &str, slot: &str) -> String {
        match slot {
            "new" => format!("{}_{}", self.func_prefix, api_snake),
            "new_impl" => format!("{}_{}_impl", self.func_prefix, api_snake),
            _ => self.c_func(api_snake, slot),
        }
    }

    /// C sentinel-macro spelling for a handle's "invalid" value
    /// (ImageHandle -> FL_IMAGE_HANDLE_INVALID): the type prefix SHOUTY-cased,
    /// then the SHOUTY type name.
    pub fn c_handle_sentinel(&self, idl_name: &str) -> String {
        format!(
            "{}_{}_INVALID",
            self.type_prefix.to_shouty_snake_case(),
            idl_name.to_shouty_snake_case()
        )
    }
}

/// The built-in flowi profile.
pub const FL: Naming = Naming {
    type_prefix: Cow::Borrowed("Fl"),
    func_prefix: Cow::Borrowed("fl"),
    string_type: None,
    string_include: None,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fl_profile_spellings() {
        assert_eq!(FL.c_type("Cursor"), "FlCursor");
        assert_eq!(FL.c_type("CursorShape"), "FlCursorShape");
        assert_eq!(
            FL.c_enumerator("CursorShape", "Arrow"),
            "FlCursorShape_Arrow"
        );
        assert_eq!(FL.c_func("cursor", "set"), "fl_cursor_set");
    }

    #[test]
    fn primary_slot_drops_the_slot_word() {
        assert_eq!(FL.c_api_func("button", "new"), "fl_button");
        assert_eq!(FL.c_api_func("button", "new_impl"), "fl_button_impl");
        assert_eq!(FL.c_api_func("button", "image"), "fl_button_image");
        let rp = Naming::new("Rp", "rp");
        assert_eq!(rp.c_api_func("button", "new"), "rp_button");
    }

    #[test]
    fn pinned_string_type_overrides_the_prefixed_default() {
        assert_eq!(FL.c_string_type(), "FlString");
        let mut rp = Naming::new("Rp", "rp");
        assert_eq!(rp.c_string_type(), "RpString");
        rp.string_type = Some(Cow::Borrowed("FlString"));
        assert_eq!(rp.c_string_type(), "FlString");
    }

    #[test]
    fn a_second_profile_swaps_the_prefix() {
        let rp = Naming::new("Rp", "rp");
        assert_eq!(rp.c_type("Cursor"), "RpCursor");
        assert_eq!(
            rp.c_enumerator("CursorShape", "Arrow"),
            "RpCursorShape_Arrow"
        );
        assert_eq!(rp.c_func("cursor", "set"), "rp_cursor_set");
    }

    #[test]
    fn handle_sentinel_spelling_follows_the_profile() {
        assert_eq!(
            FL.c_handle_sentinel("ImageHandle"),
            "FL_IMAGE_HANDLE_INVALID"
        );
        let rp = Naming::new("Rp", "rp");
        assert_eq!(
            rp.c_handle_sentinel("ImageHandle"),
            "RP_IMAGE_HANDLE_INVALID"
        );
    }
}
