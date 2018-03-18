pub mod unitlike_copy {
    macro_rules! make_unit_struct {
        ($($Name:ident)*) => {$(
            /// Unit-like struct that implements Copy, for tests.
            #[derive(Debug, Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Default)]
            pub struct $Name;

            #[allow(unused)] // they're for tests, who cares
            impl $Name {
                /// Inherent method used to verify that type inference is not necessary
                /// for rustc to prove that a given value has this type.
                ///
                /// Attempting to call this method on a value that requires type inference
                /// will result in a "Type annotations needed" error.  Calling it with an
                /// argument of the wrong type will cause a type error.
                pub fn is_known_to_be(self, _: $Name) { }
            }
        )*};
    }
    make_unit_struct!{A B C D E F}
}

pub mod unitlike_move {
    macro_rules! make_unit_struct {
        ($($Name:ident)*) => {$(
            /// Unit-like struct that does not implement, for tests.
            #[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Default)]
            pub struct $Name;

            #[allow(unused)] // they're for tests, who cares
            impl $Name {
                /// Inherent method used to verify that type inference is not necessary
                /// for rustc to prove that a given value has this type.
                ///
                /// Attempting to call this method on a value that requires type inference
                /// will result in a "Type annotations needed" error.  Calling it with an
                /// argument of the wrong type will cause a type error.
                pub fn is_known_to_be(self, _: $Name) { }
                /// `is_known_to_be` for references.
                pub fn is_known_to_be_ref(&self, _: &$Name) { }
                /// `is_known_to_be` for mutable references.
                pub fn is_known_to_be_mut(&mut self, _: &mut $Name) { }
            }
        )*};
    }
    make_unit_struct!{A B C D E F}
}
