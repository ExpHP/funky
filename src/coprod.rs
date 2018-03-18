//! The coproduct: A variadic, type-indexed sum type.
//!
//! > A "sum?" Don't be silly!

use ::unary::{IsUnary, Zero, Succ};
use ::either::{Either, Left, Right};
use ::hlist::{IsHList, HCons, HNil, PopSeq, IsSculptor};

/// Empty coproduct. A value of this type cannot exist, but we give it some methods anyways.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CVoid {}

/// Either A, or something else.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CProd<A, Rest: IsCoprod> {
    This(A),
    Those(Rest),
}
pub use CProd::{This, Those};

//----------------------------------------------------------------------------

pub trait IsCoprod {
    type Arity: IsUnary;
    const ARITY: u32 = Self::Arity::VALUE;
}

impl IsCoprod for CVoid {
    type Arity = Zero;
}

impl<A, Rest: IsCoprod> IsCoprod for CProd<A, Rest> {
    type Arity = Succ<Rest::Arity>;
}

//----------------------------------------------------------------------------

/// Unified documentation for the inherent methods shared by `CVoid` and `CProd`.
///
/// (not that you can really call any methods on a `CVoid`...)
///
/// **This trait is only for documentation.** To prevent you from using it in your
/// own code, it is sealed and has a type parameter that you cannot name.
///
/// This broadly documents the interface that is immediately available on
/// any coproduct without needing to import any traits.
///
/// Although each of these methods are actually implemented on their own,
/// smaller trait, the methods on those traits tend to have type parameters in
/// less convenient locations (e.g. on the trait itself rather than the method),
/// and ultimately, those methods are really not designed for direct use by the
/// user (only for generic bounds). You should consider the signatures here to
/// represent the true public API of coproducts.
pub trait CoprodDocumentation<IgnoreMePlease: private::Unnameable>
        : Sized
        + private::Sealed
{
    /// Borrow the value at a position, if that is the variant that is present.
    ///
    /// The index is checked at compile time.
    #[inline(always)]
    fn at<I: IsUnary>(&self, index: I) -> Option<&<Self as At<I>>::Value>
    where Self: At<I>,
    { At::at(self, index) }

    /// Mutably borrow the value at a position, if that is the variant that is present.
    ///
    /// The index is checked at compile time.
    #[inline(always)]
    fn at_mut<I: IsUnary>(&mut self, index: I) -> Option<&mut <Self as At<I>>::Value>
    where Self: At<I>,
    { At::at_mut(self, index) }

    // FIXME: This gives "the trait `coprod::PluckAt` cannot be made into an object",
    //        (why the hell does the compiler even care?! There is already a `Sized` bound!)
    // // TODO DOC
    // #[inline(always)]
    // fn pluck_at<I: IsUnary>(self, index: I) -> Either<TyAt<I, Self>, TyPluckAtRemainder<I, Self>>
    // where Self: PluckAt<I>,
    // { PluckAt::pluck_at(self, index) }

    /// Sculpt using indices previously obtained via `sculptor_of::<Ts, _>()`.
    ///
    /// The input is checked at compile time, and the output type is determined
    /// directly from the input, rather than through type inference.
    #[inline(always)]
    fn sculpt_at<S: IsSculptor>(
        self,
        sculptor: S,
    ) -> Either<TySculptAt<S, Self>, TySculptAtRemainder<S, Self>>
    where Self: SculptAt<S>,
    { SculptAt::sculpt_at(self, sculptor) }

    /// Look up the index of a type.
    ///
    /// The correct syntax is:
    ///
    /// ```ignore
    /// let index = list.index_of::<bool, _>();
    /// ```
    ///
    /// The second type parameter is unfortunate, but unavoidable.
    ///
    /// As long as there is a unique instance of the type in the list,
    /// type inference can infer the index. The index can be used
    /// as an argument to e.g. `at` or `pop_at` on another list.
    ///
    /// It is checked at compile time that the type is contained in the list.
    #[inline(always)]
    fn index_of<T, Index: IsUnary>(&self) -> Index
    where Self: Locate<T, Index>,
    { Self::static_index() }

    // TODO DOC
    #[inline(always)]
    fn sculptor_of<Ts: IsCoprod, S: IsSculptor>(&self) -> S
    where Self: Sculpt<Ts, S>,
    { Self::static_sculptor() }

    // TODO DOC
    #[inline(always)]
    fn inject<T, N: IsUnary>(x: T) -> Self
    where Self: Inject<T, N>,
    { Inject::inject(x) }

    // TODO DOC
    // NOTE TO SELF: The reason why this method can use `inject` while seemingly
    //      similar methods like `at` require their own trait is because the
    //      type-indexed forms of those methods return a type parameter
    //      (so the new trait is needed to turn it into an associated type).
    //      In contrast, `inject` returns the known type Self.
    #[inline(always)]
    fn inject_at<T, N: IsUnary>(_index: N, x: T) -> Self
    where Self: Inject<T, N>,
    { Inject::inject(x) }

    #[inline(always)]
    fn embed<Bs: IsCoprod, N: IsHList>(self) -> Bs
    where Self: Embed<Bs, N>,
    { Embed::embed(self) }
}

/// Free function form to create a Coprod of inferred type.
#[inline(always)]
pub fn inject<C: Inject<T, N>, N: IsUnary, T>(x: T) -> C
{ C::inject(x) }

impl<Choices: private::Sealed> CoprodDocumentation<private::Ambiguous1> for Choices { }
impl<Choices: private::Sealed> CoprodDocumentation<private::Ambiguous2> for Choices { }

type A1 = private::Ambiguous1;
mod private {
    use super::*;

    pub struct Ambiguous1 {}
    pub struct Ambiguous2 {}

    pub trait Unnameable {}
    impl Unnameable for Ambiguous1 {}
    impl Unnameable for Ambiguous2 {}

    pub trait Sealed: IsCoprod {}
    impl Sealed for CVoid {}
    impl<A, Rest: IsCoprod> Sealed for CProd<A, Rest> {}
}

//----------------------------------------------------------------------------

macro_rules! gen_stubs {
    ($($tok:tt)*)
    => {
        $($tok)* {
            // NOTE: All methods delegate to the methods on the Documentation trait so
            //       that the methods of Documentation are properly typechecked to be
            //       consistent with the exposed API.

            // FIXME FIX NAMES IN LINKS

            /// See [`CoprodDocumentation::at`](../struct.CoprodDocumentation.html#method.at).
            #[inline(always)]
            pub fn at<I: IsUnary>(&self, index: I) -> Option<&<Self as At<I>>::Value>
            where Self: At<I>,
            { CoprodDocumentation::<A1>::at::<I>(self, index) }

            /// See [`CoprodDocumentation::at_mut`](../struct.CoprodDocumentation.html#method.at_mut).
            #[inline(always)]
            pub fn at_mut<I: IsUnary>(&mut self, index: I) -> Option<&mut <Self as At<I>>::Value>
            where Self: At<I>,
            { CoprodDocumentation::<A1>::at_mut::<I>(self, index) }

            // /// See [`CoprodDocumentation::pluck_at`](../struct.CoprodDocumentation.html#method.pluck_at).
            // #[inline(always)]
            // pub fn pluck_at<I: IsUnary>(self, index: I) -> Either<TyAt<I, Self>, TyPluckAtRemainder<I, Self>>
            // where Self: PluckAt<I>,
            // { CoprodDocumentation::pluck_at::<I>(self, index) }

            /// See [`CoprodDocumentation::pop_at`](../struct.CoprodDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn sculpt_at<S: IsSculptor>(
                self,
                sculptor: S,
            ) -> Either<TySculptAt<S, Self>, TySculptAtRemainder<S, Self>>
            where Self: SculptAt<S>,
            { CoprodDocumentation::<A1>::sculpt_at::<S>(self, sculptor) }

            /// See [`CoprodDocumentation::pop_at`](../struct.CoprodDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn index_of<T, Index: IsUnary>(&self) -> Index
            where Self: Locate<T, Index>,
            { CoprodDocumentation::<A1>::index_of::<T, Index>(self) }

            /// See [`CoprodDocumentation::pop_at`](../struct.CoprodDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn sculptor_of<Ts: IsCoprod, S: IsSculptor>(&self) -> S
            where Self: Sculpt<Ts, S>,
            { CoprodDocumentation::<A1>::sculptor_of::<Ts, S>(self) }

            #[inline(always)]
            pub fn inject<T, N: IsUnary>(x: T) -> Self
            where Self: Inject<T, N>,
            { CoprodDocumentation::<A1>::inject(x) }

            #[inline(always)]
            pub fn inject_at<T, N: IsUnary>(index: N, x: T) -> Self
            where Self: Inject<T, N>,
            { CoprodDocumentation::<A1>::inject_at(index, x) }

            #[inline(always)]
            pub fn embed<Bs: IsCoprod, N: IsHList>(self) -> Bs
            where Self: Embed<Bs, N>,
            { CoprodDocumentation::<A1>::embed(self) }
        }
    };
}

gen_stubs!{impl<A, Rest: IsCoprod> CProd<A, Rest>}
gen_stubs!{impl CVoid}

//----------------------------------------------------------------------------
// Index-based lookup.

pub type TyAt<N, List> = <List as At<N>>::Value;
pub trait At<Index: IsUnary>: IsCoprod {
    type Value;

    fn at(&self, index: Index) -> Option<&Self::Value>;

    fn at_mut(&mut self, index: Index) -> Option<&mut Self::Value>;
}

impl<A, Rest: IsCoprod> At<Zero> for CProd<A, Rest> {
    type Value = A;

    #[inline]
    fn at(&self, Zero: Zero) -> Option<&Self::Value>
    { match *self {
        This(ref it) => Some(it),
        Those(_) => None,
    }}

    #[inline]
    fn at_mut(&mut self, Zero: Zero) -> Option<&mut Self::Value>
    { match *self {
        This(ref mut it) => Some(it),
        Those(_) => None,
    }}
}

impl<A, Rest: IsCoprod, N: IsUnary, V> At<Succ<N>> for CProd<A, Rest>
where Rest: At<N, Value=V>,
{
    type Value = V;

    #[inline]
    fn at(&self, sn: Succ<N>) -> Option<&Self::Value>
    { match *self {
       This(_) => None,
       Those(ref those) => those.at(sn.pred()),
    }}

    #[inline]
    fn at_mut(&mut self, sn: Succ<N>) -> Option<&mut Self::Value>
    { match *self {
       This(_) => None,
       Those(ref mut those) => those.at_mut(sn.pred()),
    }}
}

//----------------------------------------------------------------------------

pub type TyPluckAtRemainder<N, List> = PluckRemainderT<TyAt<N, List>, N, List>;
pub trait PluckAt<Index: IsUnary>
        : Sized
        + At<Index>
        + Pluck<TyAt<Index, Self>, Index>
{
    #[inline(always)]
    fn take_at(self, _: Index) -> Either<Self::Value, Self::Remainder>
    { self.pluck() }
}

impl<N: IsUnary, List> PluckAt<N> for List
where Self: At<N> + Pluck<TyAt<N, Self>, N>,
{ }

//----------------------------------------------------------------------------

#[test]
fn indexing_ops_dont_require_type_inference() {
    // use unary::consts::*;
    // use ::test_structs::unitlike_move::{A, B, C};

    // // Types
    // let mut abc = hlist![A, B, C];
    // abc.at(P0).is_known_to_be_ref(&A);
    // abc.at(P1).is_known_to_be_ref(&B);
    // abc.at(P2).is_known_to_be_ref(&C);
    // abc.at_mut(P0).is_known_to_be_mut(&mut A);
    // abc.at_mut(P1).is_known_to_be_mut(&mut B);
    // abc.at_mut(P2).is_known_to_be_mut(&mut C);

    // let (a, hlist_pat![b, c]) = abc.clone().pop_at(P0);
    // a.is_known_to_be(A);
    // b.is_known_to_be(B);
    // c.is_known_to_be(C);

    // let (b, hlist_pat![a, c]) = abc.clone().pop_at(P1);
    // a.is_known_to_be(A);
    // b.is_known_to_be(B);
    // c.is_known_to_be(C);

    // let (c, hlist_pat![a, b]) = abc.clone().pop_at(P2);
    // a.is_known_to_be(A);
    // b.is_known_to_be(B);
    // c.is_known_to_be(C);
    panic!()
}

#[test]
fn indexing_ops_are_not_confused_by_equal_types() {
    // use unary::consts::*;

    // #[derive(Debug, Copy, Clone, PartialEq, Eq)] struct X(i32);

    // // Values
    // let mut list = hlist![X(0), X(1), X(2)];
    // assert_eq!(list.at(P0),     &X(0));
    // assert_eq!(list.at_mut(P0), &mut X(0));
    // assert_eq!(list.pop_at(P0), (X(0), hlist![X(1), X(2)]));
    // assert_eq!(list.at(P1),     &X(1));
    // assert_eq!(list.at_mut(P1), &mut X(1));
    // assert_eq!(list.pop_at(P1), (X(1), hlist![X(0), X(2)]));
    // assert_eq!(list.at(P2),     &X(2) );
    // assert_eq!(list.at_mut(P2), &mut X(2));
    // assert_eq!(list.pop_at(P2), (X(2), hlist![X(0), X(1)]));
    panic!()
}

//----------------------------------------------------------------------------
// type-directed lookup

/// Trait for getting references to items by type.
///
/// It might seem a bit unusual that `Index` is a type parameter rather than
/// an associated type. In fact, it *has* to be, because otherwise the impls
/// for `CProd` would conflict with each other.  In practice, type inference
/// is perfectly capable of inferring the `Index` so that it can be largely
/// ignored.
pub trait Locate<T, Index: IsUnary>: IsCoprod {
    #[inline(always)]
    fn static_index() -> Index
    { Default::default() }

    fn get(&self) -> Option<&T>;

    fn get_mut(&mut self) -> Option<&mut T>;
}

pub type PluckRemainderT<T, N, List> = <List as Pluck<T, N>>::Remainder;

pub trait Pluck<T, Index: IsUnary>: Locate<T, Index> {
    type Remainder: IsCoprod;

    fn pluck(self) -> Either<T, Self::Remainder>;
}

impl<A, As: IsCoprod> Locate<A, Zero> for CProd<A, As> {
    #[inline]
    fn get(&self) -> Option<&A>
    { match *self {
        This(ref this) => Some(this),
        Those(_) => None,
    }}

    #[inline]
    fn get_mut(&mut self) -> Option<&mut A>
    { match *self {
        This(ref mut this) => Some(this),
        Those(_) => None,
    }}
}

impl<T, A, As: IsCoprod, N: IsUnary> Locate<T, Succ<N>> for CProd<A, As>
where As: Locate<T, N>,
{
    #[inline]
    fn get(&self) -> Option<&T>
    { match *self {
        This(_) => None,
        Those(ref those) => those.get(),
    }}

    #[inline]
    fn get_mut(&mut self) -> Option<&mut T>
    { match *self {
        This(_) => None,
        Those(ref mut those) => those.get_mut(),
    }}
}

impl<A, As: IsCoprod> Pluck<A, Zero> for CProd<A, As> {
    type Remainder = As;

    #[inline]
    fn pluck(self) -> Either<A, Self::Remainder>
    { match self {
        This(this) => Left(this),
        Those(those) => Right(those),
    }}
}

impl<T, A, As: IsCoprod, N: IsUnary> Pluck<T, Succ<N>> for CProd<A, As>
where As: Pluck<T, N>,
{
    type Remainder = CProd<A, As::Remainder>;

    #[inline]
    fn pluck(self) -> Either<T, Self::Remainder>
    { match self {
        Those(those) => those.pluck().map_right(Those),
        This(this) => Right(This(this)),
    }}
}

#[test]
fn test_single_type_lookup() {
    // use ::test_structs::unitlike_move::{A, B, C};

    // let &A = hlist![A, B, C].locate();
    // let &B = hlist![A, B, C].locate();
    // let &C = hlist![A, B, C].locate();
    // let &mut A = hlist![A, B, C].locate_mut();
    // let &mut B = hlist![A, B, C].locate_mut();
    // let &mut C = hlist![A, B, C].locate_mut();

    // let (A, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    // r1.is_known_to_be(B);
    // r2.is_known_to_be(C);

    // let (B, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    // r1.is_known_to_be(A);
    // r2.is_known_to_be(C);

    // let (C, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    // r1.is_known_to_be(A);
    // r2.is_known_to_be(B);

    // TODO: compile-fail
    // let &A = hlist![A, A].locate(); //~ ERROR type annotations required
    // TODO: compile-fail
    // let &A = hlist![B, C].locate(); //~ ERROR trait bound
    panic!()
}

#[test]
fn test_reuse_index() {
    // use ::test_structs::unitlike_move::*;
    // let abc = hlist![A, B, C];
    // let mut def = hlist![D, E, F];

    // def.at(abc.index_of::<A, _>()).is_known_to_be_ref(&D);
    // def.at(abc.index_of::<B, _>()).is_known_to_be_ref(&E);
    // def.at(abc.index_of::<C, _>()).is_known_to_be_ref(&F);
    // def.at_mut(abc.index_of::<A, _>()).is_known_to_be_mut(&mut D);
    // def.at_mut(abc.index_of::<B, _>()).is_known_to_be_mut(&mut E);
    // def.at_mut(abc.index_of::<C, _>()).is_known_to_be_mut(&mut F);

    // TODO: compile-fail
    // let index = hlist![A, B, C].index_of::<A, _>();
    // def.at(abc.index_of::<A, _>()).is_known_to_be_ref(&E); //~ ERROR mismatched types
    panic!()
}

//----------------------------------------------------------------------------

// I tried a variety of designs for this, but couldn't come up with anything
// where type inference is actually capable of driving the entire computation.
//
// pub trait LocateAll<T, Mask> {
//     #[inline(always)]
//     fn mask(&self) -> Mask
//     { Self::static_mask() }
//
//     fn static_mask() -> Mask;
// }

//----------------------------------------------------------------------------

pub type TySculptRemainder<Ts, Is, List> = <List as Sculpt<Ts, Is>>::Remainder;
pub trait Sculpt<Targets, S: IsSculptor>: Sized + IsCoprod {
    type Remainder: IsCoprod;

    fn sculpt(self) -> Either<Targets, Self::Remainder>;

    fn static_sculptor() -> S;
}

pub type TySculptAt<S, List> = <List as SculptAt<S>>::Sculpted;
pub type TySculptAtRemainder<S, List> = <List as Sculpt<TySculptAt<S, List>, S>>::Remainder;
pub trait SculptAt<S: IsSculptor>: Sculpt<<Self as SculptAt<S>>::Sculpted, S> {
    type Sculpted;

    #[inline(always)]
    fn sculpt_at(self, _: S) -> Either<Self::Sculpted, Self::Remainder>
    { self.sculpt() }
}

impl<Choices: IsCoprod, T, Ts: IsCoprod, N: IsUnary, Ns: IsHList, Rem>
    Sculpt<CProd<T, Ts>, PopSeq<HCons<N, Ns>>> for Choices
where
    Self: Pluck<T, N, Remainder=Rem>,
    Rem: Sculpt<Ts, PopSeq<Ns>>,
{
    type Remainder = TySculptRemainder<Ts, PopSeq<Ns>, Rem>;

    #[inline]
    fn sculpt(self) -> Either<CProd<T, Ts>, Self::Remainder>
    { match self.pluck() {
        Left(good) => Left(This(good)),
        Right(bads) => match bads.sculpt() {
            Left(goods) => Left(Those(goods)),
            Right(bads) => Right(bads),
        }
    }}

    #[inline(always)]
    fn static_sculptor() -> PopSeq<HCons<N, Ns>>
    {
        let idx = <Self>::static_index();
        let PopSeq(idxs) = <PluckRemainderT<T, N, Self>>::static_sculptor();
        PopSeq(HCons(idx, idxs))
    }
}

impl<Choices: IsCoprod> Sculpt<CVoid, PopSeq<HNil>> for Choices {
    type Remainder = Self;

    #[inline(always)]
    fn sculpt(self) -> Either<CVoid, Self::Remainder>
    { Right(self) }

    #[inline(always)]
    fn static_sculptor() -> PopSeq<HNil>
    { PopSeq(HNil) }
}

impl<
    Choices: IsCoprod,
    Ts: IsCoprod,
    N: IsUnary, Ns: IsHList,
> SculptAt<PopSeq<HCons<N, Ns>>> for Choices
where
    Self: PluckAt<N>,
    TyPluckAtRemainder<N, Self>: SculptAt<PopSeq<Ns>, Sculpted=Ts>,
{
    type Sculpted = CProd<TyAt<N, Self>, Ts>;
}

impl<Choices: IsCoprod> SculptAt<PopSeq<HNil>> for Choices {
    type Sculpted = CVoid;
}

#[test]
fn sculpt_nothing() {
    // use ::test_structs::unitlike_move::{A, B};
    // let (HNil, HNil) = HNil.sculpt();
    // let (HNil, hlist_pat![A, B]) = hlist![A, B].sculpt();
    // let (HNil, HNil) = HNil.sculpt_at(PopSeq(HNil));
    // let (HNil, hlist_pat![A, B]) = hlist![A, B].sculpt_at(PopSeq(HNil));
    panic!()
}

#[test]
fn sculpt_at_doesnt_require_type_inference() {
    // use ::test_structs::unitlike_move::{A, B, C, D, E};

    // let abcde = hlist![A, B, C, D, E];
    // let sculptor = abcde.sculptor_of::<HList![C, A, D], _>();

    // let (hlist_pat![c, a, d], hlist_pat![b, e]) = abcde.sculpt_at(sculptor);
    // a.is_known_to_be(A);
    // b.is_known_to_be(B);
    // c.is_known_to_be(C);
    // d.is_known_to_be(D);
    // e.is_known_to_be(E);
    panic!()
}

//----------------------------------------------------------------------------

pub trait Inject<T, Index: IsUnary> {
    fn inject(x: T) -> Self;
}

impl<A, As: IsCoprod> Inject<A, Zero> for CProd<A, As> {
    #[inline]
    fn inject(a: A) -> CProd<A, As>
    { This(a) }
}

impl<T, A, As: IsCoprod, N: IsUnary> Inject<T, Succ<N>> for CProd<A, As>
where As: Inject<T, N>,
{
    #[inline]
    fn inject(x: T) -> CProd<A, As>
    { Those(As::inject(x)) }
}

pub trait Embed<Choices: IsCoprod, Indices: IsHList> {
    fn embed(self) -> Choices;
}

impl<Bs: IsCoprod> Embed<Bs, HNil> for CVoid {
    #[inline]
    fn embed(self) -> Bs
    { match self {
        // impossible!
    }}
}

impl<A, As: IsCoprod, Bs: IsCoprod, N: IsUnary, Ns: IsHList>
    Embed<Bs, HCons<N, Ns>>
    for CProd<A, As>
where
    Bs: Inject<A, N>,
    As: Embed<Bs, Ns>,
{
    #[inline]
    fn embed(self) -> Bs
    { match self {
        This(this) => Bs::inject(this),
        Those(those) => those.embed(),
    }}
}

#[test]
fn test_embed() {
    use ::test_structs::unitlike_move::{A, B, C, D, E};
    use ::unary::consts::{P0, P1};
    fn falsum() -> bool { false };

    // identity
    let embedded: Coprod![A, B, C] = <Coprod![A, B, C]>::inject(A).embed();
    assert_matches!(This(A), embedded);

    // into superset
    let embedded: Coprod![A, B, C, D, E] = <Coprod![A, B, C]>::inject(A).embed();
    assert_matches!(This(A), embedded);

    // order doesn't matter
    let embedded: Coprod![A, D, B, C] = <Coprod![C, B, A]>::inject(A).embed();
    assert_matches!(This(A), embedded);
    let embedded: Coprod![C, A, D, B] = <Coprod![C, B, A]>::inject(A).embed();
    assert_matches!(Those(This(A)), embedded);

    // The input type can have repeats!
    let embedded: Coprod![A, B, C] = <Coprod![B, B, B, B]>::inject_at(P0, B).embed();
    assert_matches!(Those(This(B)), embedded);

    let embedded: Coprod![A, B, C] = <Coprod![B, B, B, B]>::inject_at(P1, B).embed();
    assert_matches!(Those(This(B)), embedded);

    if falsum() {
        #[allow(unreachable_code)] {
            #[allow(unused)]
            let void: CVoid = panic!();
            let _: Coprod![A, B, C] = void.embed();
            let _: Coprod![] = void.embed();
        }
    }

    // TODO: compile-fail
    // missing B
    // let This(A): Coprod![A, C, D, E] = <Coprod![A, B, C]>::inject(A).embed();
}

//----------------------------------------------------------------------------
