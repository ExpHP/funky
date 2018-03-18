
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


#[test]
fn test_hlist_macros() {
    struct A;
    struct B;
    struct C;

    // trailing comma support
    let hlist_pat![]: HList![] = hlist![];
    let hlist_pat![A]: HList![A] = hlist![A];
    let hlist_pat![A,]: HList![A,] = hlist![A,];
    let hlist_pat![A, B]: HList![A, B] = hlist![A, B];
    let hlist_pat![A, B,]: HList![A, B,] = hlist![A, B,];

    // '/Rest' accepted locations,
    // and consistency between the three macros (checked with types)
    let hlist_pat![/hlist_pat![C]]: HList![/HList![C]] = hlist![/ hlist![C]];
    let hlist_pat![A, /hlist_pat![C]]: HList![A, /HList![C]] = hlist![A, / hlist![C]];
    let hlist_pat![A, B, /hlist_pat![C]]: HList![A, B, /HList![C]] = hlist![A, B, / hlist![C]];

    // '/Rest' semantics
    let rest = hlist![B, C];
    let hlist_pat![A, B, C] = hlist![A, /rest];

    let hlist_pat![A, /rest] = hlist![A, B, C];
    let hlist_pat![B, C] = rest;
}
