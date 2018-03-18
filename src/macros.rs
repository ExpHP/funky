
#[macro_export]
macro_rules! hlist {
    () => { $crate::HNil };
    (/ $rest:expr) => { $rest };
    ($a:expr) => { hlist![$a,] };
    ($a:expr, $($tok:tt)*) => { $crate::HCons($a, hlist![$($tok)*]) };
}

#[macro_export]
macro_rules! hlist_pat {
    () => { $crate::HNil };
    (/ $rest:pat) => { $rest };
    ($a:pat) => { hlist_pat![$a,] };
    ($a:pat, $($tok:tt)*) => { $crate::HCons($a, hlist_pat![$($tok)*]) };
}

#[macro_export]
macro_rules! HList {
    () => { $crate::HNil };
    (/ $Rest:ty) => { $Rest };
    ($A:ty) => { HList![$A,] };
    ($A:ty, $($tok:tt)*) => { $crate::HCons<$A, HList![$($tok)*]> };
}

#[macro_export]
macro_rules! Coprod {
    () => { $crate::CVoid };
    (/ $Rest:ty) => { $Rest };
    ($A:ty) => { Coprod![$A,] };
    ($A:ty, $($tok:tt)*) => { $crate::CProd<$A, Coprod![$($tok)*]> };
}

#[cfg(test)]
macro_rules! assert_matches {
    ($pat:pat, $expr:expr,)
    => { assert_matches!($pat, $expr) };
    ($pat:pat, $expr:expr)
    => { assert_matches!($pat, $expr, "actual {:?}", $expr) };
    ($pat:pat, $expr:expr, $($arg:expr),+ $(,)*)
    => {
        match $expr {
            $pat => {},
            _ => panic!(
                "assertion failed: {} ({})",
                stringify!(assert_matches!($pat, $expr)),
                format_args!($($arg),+))
        }
    };
}

#[test]
fn test_hlist_macros() {
    use ::coprod::inject;
    use ::test_structs::unitlike_copy::{A, B, C};

    let falsum = || false;

    // trailing comma support
    let hlist_pat![]: HList![] = hlist![];
    let hlist_pat![A]: HList![A] = hlist![A];
    let hlist_pat![A,]: HList![A,] = hlist![A,];
    let hlist_pat![A, B]: HList![A, B] = hlist![A, B];
    let hlist_pat![A, B,]: HList![A, B,] = hlist![A, B,];

    if falsum() { let _: Coprod![] = panic!(); }
    if falsum() { let _: Coprod![A] = panic!(); }
    if falsum() { let _: Coprod![A,] = panic!(); }
    if falsum() { let _: Coprod![A, B] = panic!(); }
    if falsum() { let _: Coprod![A, B,] = panic!(); }

    // '/Rest' accepted locations,
    // and consistency between the three macros (checked with types)
    let hlist_pat![/hlist_pat![C]]: HList![/HList![C]] = hlist![/ hlist![C]];
    let hlist_pat![A, /hlist_pat![C]]: HList![A, /HList![C]] = hlist![A, / hlist![C]];
    let hlist_pat![A, B, /hlist_pat![C]]: HList![A, B, /HList![C]] = hlist![A, B, / hlist![C]];

    // '/Rest' semantics
    let hlist_pat![A, B, C] = hlist![A, /hlist![B, C]];
    let hlist_pat![A, /hlist_pat![B, C]] = hlist![A, B, C];

    // accepted locations and semantics in Coprod
    let choice: Coprod![A, B, C] = inject(A);
    let _: Coprod![/Coprod![A, B, C]] = choice;
    let _: Coprod![A, /Coprod![B, C]] = choice;
    let _: Coprod![A, B, /Coprod![C]] = choice;
}
