use ::unary::{IsUnary, Zero, Succ};

/// Empty IsHList.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct HNil;
/// An IsHList whose first item is of type `A`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct HCons<A, Rest: IsHList>(pub A, pub Rest);

//----------------------------------------------------------------------------

pub trait IsHList {
    type Length: IsUnary;
    const LENGTH: u32 = Self::Length::VALUE;
}

impl IsHList for HNil {
    type Length = Zero;
    const LENGTH: u32 = Self::Length::VALUE;
}

impl<A, Rest: IsHList> IsHList for HCons<A, Rest> {
    type Length = Succ<Rest::Length>;
    const LENGTH: u32 = Self::Length::VALUE;
}

//----------------------------------------------------------------------------

/// Unified documentation for the inherent methods shared by `HCons` and `HNil`.
///
/// This broadly documents the interface that is immediately available on
/// any HList without needing to import any traits.
///
/// Although each of these methods are actually implemented on their own,
/// smaller trait, the methods on those traits tend to have type parameters in
/// less convenient locations (e.g. on the trait itself rather than the method),
/// and ultimately, those methods are really not designed for direct use by the
/// user (only for generic bounds). You should consider the signatures here to
/// represent the true public API of HLists.
pub trait HListDocumentation {
    /// Borrow the value at a position.
    ///
    /// The index is checked at compile time.
    #[inline(always)]
    fn at<I: IsUnary>(&self, index: I) -> &<Self as At<I>>::Value
    where Self: At<I>,
    { At::at(self, index) }

    /// Mutably borrow the value at a position.
    ///
    /// The index is checked at compile time.
    #[inline(always)]
    fn at_mut<I: IsUnary>(&mut self, index: I) -> &mut <Self as At<I>>::Value
    where Self: At<I>,
    { At::at_mut(self, index) }

    /// Remove the value at a position.
    ///
    /// The index is checked at compile time.
    #[inline(always)]
    fn pop_at<I: IsUnary>(self, index: I) -> (TyAt<I, Self>, TyPopAtRemainder<I, Self>)
    where Self: PopAt<I>,
    { PopAt::pop_at(self, index) }

    /// Sculpt using indices previously obtained via `sculptor_of::<Ts, _>()`.
    ///
    /// The input is checked at compile time, and the output type is determined
    /// directly from the input, rather than through type inference.
    #[inline(always)]
    fn sculpt_at<S: IsSculptor>(
        self,
        sculptor: S,
    ) -> (TySculptAt<S, Self>, TySculptAtRemainder<S, Self>)
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

    /// Look up the pop-sequence for `sculpt`-ing an HList.
    ///
    /// This fails at compile time if `Ts` cannot be `sculpt`-ed from `Self`.
    ///
    /// Typically, correct usage requires the use of a turbofish to supply the
    /// type parameter `Ts`. Similarly to `index_of`, the second type parameter
    /// should be supplied as `_`, allowing type inference to compute it.
    ///
    /// ```rust
    /// # #[macro_use] extern crate funky;
    /// # fn main() {
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct A1;
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct A2;
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct A3;
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct B1;
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct B2;
    /// #[derive(Debug, PartialEq, Copy, Clone)] struct B3;
    ///
    /// let list_a = hlist![A1, A2, A3];
    /// let list_b = hlist![B1, B2, B3];
    ///
    /// // find the indices for sculpting
    /// let sculptor = list_a.sculptor_of::<HList![A3, A1], _>();
    ///
    /// // Apply them to both lists.
    /// let (hlist_pat![A3, A1], hlist_pat![A2]) = list_a.sculpt_at(sculptor);
    /// let (hlist_pat![B3, B1], hlist_pat![B2]) = list_b.sculpt_at(sculptor);
    ///
    /// // Notice that the type of `list_b.sculpt_at(sculptor)` is always
    /// // immediately known, without any help from type inference;
    /// // The following does not produce a "Type annotations needed" error.
    /// assert_eq!(list_b.sculpt_at(sculptor), list_b.sculpt_at(sculptor));
    /// # }
    /// ```
    #[inline(always)]
    fn sculptor_of<Ts: IsHList, S: IsSculptor>(&self) -> S
    where Self: Sculpt<Ts, S>,
    { Self::static_sculptor() }
}

impl<A, Rest: IsHList> HListDocumentation for HCons<A, Rest> { }
impl HListDocumentation for HNil { }

//----------------------------------------------------------------------------

macro_rules! gen_stubs {
    ($($tok:tt)*)
    => {
        $($tok)* {
            // NOTE: All methods delegate to the methods on the Documentation trait so
            //       that the methods of Documentation are properly typechecked to be
            //       consistent with the exposed API.

            /// See [`HListDocumentation::at`](../struct.HListDocumentation.html#method.at).
            #[inline(always)]
            pub fn at<I: IsUnary>(&self, index: I) -> &<Self as At<I>>::Value
            where Self: At<I>,
            { HListDocumentation::at::<I>(self, index) }

            /// See [`HListDocumentation::at_mut`](../struct.HListDocumentation.html#method.at_mut).
            #[inline(always)]
            pub fn at_mut<I: IsUnary>(&mut self, index: I) -> &mut <Self as At<I>>::Value
            where Self: At<I>,
            { HListDocumentation::at_mut::<I>(self, index) }

            /// See [`HListDocumentation::pop_at`](../struct.HListDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn pop_at<I: IsUnary>(self, index: I) -> (TyAt<I, Self>, TyPopAtRemainder<I, Self>)
            where Self: PopAt<I>,
            { HListDocumentation::pop_at::<I>(self, index) }

            /// See [`HListDocumentation::pop_at`](../struct.HListDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn sculpt_at<S: IsSculptor>(
                self,
                sculptor: S,
            ) -> (TySculptAt<S, Self>, TySculptAtRemainder<S, Self>)
            where Self: SculptAt<S>,
            { HListDocumentation::sculpt_at::<S>(self, sculptor) }

            /// See [`HListDocumentation::pop_at`](../struct.HListDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn index_of<T, Index: IsUnary>(&self) -> Index
            where Self: Locate<T, Index>,
            { HListDocumentation::index_of::<T, Index>(self) }

            /// See [`HListDocumentation::pop_at`](../struct.HListDocumentation.html#method.pop_at).
            #[inline(always)]
            pub fn sculptor_of<Ts: IsHList, S: IsSculptor>(&self) -> S
            where Self: Sculpt<Ts, S>,
            { HListDocumentation::sculptor_of::<Ts, S>(self) }
        }
    };
}

gen_stubs!{impl<A, Rest: IsHList> HCons<A, Rest>}
gen_stubs!{impl HNil}

//----------------------------------------------------------------------------
// Index-based lookup.

pub type TyAt<N, List> = <List as At<N>>::Value;
pub trait At<Index: IsUnary>: IsHList {
    type Value;

    fn at(&self, index: Index) -> &Self::Value;

    fn at_mut(&mut self, index: Index) -> &mut Self::Value;
}

impl<A, Rest: IsHList> At<Zero> for HCons<A, Rest> {
    type Value = A;

    #[inline(always)]
    fn at(&self, Zero: Zero) -> &Self::Value
    { &self.0 }

    #[inline(always)]
    fn at_mut(&mut self, Zero: Zero) -> &mut Self::Value
    { &mut self.0 }
}

impl<A, Rest: IsHList, N: IsUnary, V> At<Succ<N>> for HCons<A, Rest>
where Rest: At<N, Value=V>,
{
    type Value = V;

    #[inline(always)]
    fn at(&self, sn: Succ<N>) -> &Self::Value
    { self.1.at(sn.pred()) }

    #[inline(always)]
    fn at_mut(&mut self, sn: Succ<N>) -> &mut Self::Value
    { self.1.at_mut(sn.pred()) }
}

//----------------------------------------------------------------------------

pub type TyPopAtRemainder<N, List> = PluckRemainderT<TyAt<N, List>, N, List>;
pub trait PopAt<Index: IsUnary>
        : Sized
        + At<Index>
        + Pluck<TyAt<Index, Self>, Index>
{
    #[inline(always)]
    fn pop_at(self, _: Index) -> (Self::Value, Self::Remainder)
    { self.pluck() }
}

impl<N: IsUnary, List> PopAt<N> for List
where Self: At<N> + Pluck<TyAt<N, Self>, N>,
{ }

//----------------------------------------------------------------------------

#[test]
fn indexing_ops_dont_require_type_inference() {
    use unary::consts::*;
    use ::test_structs::unitlike_move::{A, B, C};

    // Types
    let mut abc = hlist![A, B, C];
    abc.at(P0).is_known_to_be_ref(&A);
    abc.at(P1).is_known_to_be_ref(&B);
    abc.at(P2).is_known_to_be_ref(&C);
    abc.at_mut(P0).is_known_to_be_mut(&mut A);
    abc.at_mut(P1).is_known_to_be_mut(&mut B);
    abc.at_mut(P2).is_known_to_be_mut(&mut C);

    let (a, hlist_pat![b, c]) = abc.clone().pop_at(P0);
    a.is_known_to_be(A);
    b.is_known_to_be(B);
    c.is_known_to_be(C);

    let (b, hlist_pat![a, c]) = abc.clone().pop_at(P1);
    a.is_known_to_be(A);
    b.is_known_to_be(B);
    c.is_known_to_be(C);

    let (c, hlist_pat![a, b]) = abc.clone().pop_at(P2);
    a.is_known_to_be(A);
    b.is_known_to_be(B);
    c.is_known_to_be(C);
}

#[test]
fn indexing_ops_are_not_confused_by_equal_types() {
    use unary::consts::*;

    #[derive(Debug, Copy, Clone, PartialEq, Eq)] struct X(i32);

    // Values
    let mut list = hlist![X(0), X(1), X(2)];
    assert_eq!(list.at(P0),     &X(0));
    assert_eq!(list.at_mut(P0), &mut X(0));
    assert_eq!(list.pop_at(P0), (X(0), hlist![X(1), X(2)]));
    assert_eq!(list.at(P1),     &X(1));
    assert_eq!(list.at_mut(P1), &mut X(1));
    assert_eq!(list.pop_at(P1), (X(1), hlist![X(0), X(2)]));
    assert_eq!(list.at(P2),     &X(2) );
    assert_eq!(list.at_mut(P2), &mut X(2));
    assert_eq!(list.pop_at(P2), (X(2), hlist![X(0), X(1)]));
}

//----------------------------------------------------------------------------
// type-directed lookup

/// Trait for getting references to items by type.
///
/// It might seem a bit unusual that `Index` is a type parameter rather than
/// an associated type. In fact, it *has* to be, because otherwise the impls
/// for `HCons` would conflict with each other.  In practice, type inference
/// is perfectly capable of inferring the `Index` so that it can be largely
/// ignored.
///
/// **_Challenge:_** Design a trait `LocateFirst<T>` that locates the first
/// item of type `T`. Now implement it for HCons. *Betcha can't.*
pub trait Locate<T, Index: IsUnary>: IsHList {
    #[inline(always)]
    fn static_index() -> Index
    { Default::default() }

    fn locate(&self) -> &T;

    fn locate_mut(&mut self) -> &mut T;
}

pub type PluckRemainderT<T, N, List> = <List as Pluck<T, N>>::Remainder;

/// Trait for removing items by type.
///
/// It might seem a bit unusual that `Index` is a type parameter rather than
/// an associated type, but it is necessary. See [`Locate`] for more discussion.
pub trait Pluck<T, Index: IsUnary>: Locate<T, Index> {
    type Remainder: IsHList;

    fn pluck(self) -> (T, Self::Remainder);
}

impl<A, As: IsHList> Locate<A, Zero> for HCons<A, As> {
    #[inline(always)]
    fn locate(&self) -> &A
    { &self.0 }

    #[inline(always)]
    fn locate_mut(&mut self) -> &mut A
    { &mut self.0 }
}

impl<T, A, As: IsHList, N: IsUnary> Locate<T, Succ<N>> for HCons<A, As>
where As: Locate<T, N>,
{
    #[inline(always)]
    fn locate(&self) -> &T
    { self.1.locate() }

    #[inline(always)]
    fn locate_mut(&mut self) -> &mut T
    { self.1.locate_mut() }
}

impl<A, As: IsHList> Pluck<A, Zero> for HCons<A, As> {
    type Remainder = As;

    #[inline(always)]
    fn pluck(self) -> (A, Self::Remainder)
    { (self.0, self.1) }
}

impl<T, A, As: IsHList, N: IsUnary> Pluck<T, Succ<N>> for HCons<A, As>
where As: Pluck<T, N>,
{
    type Remainder = HCons<A, As::Remainder>;

    #[inline(always)]
    fn pluck(self) -> (T, Self::Remainder) {
        let HCons(head, tail) = self;
        let (t, tail) = tail.pluck();
        (t, HCons(head, tail))
    }
}

#[test]
fn test_single_type_lookup() {
    use ::test_structs::unitlike_move::{A, B, C};

    let &A = hlist![A, B, C].locate();
    let &B = hlist![A, B, C].locate();
    let &C = hlist![A, B, C].locate();
    let &mut A = hlist![A, B, C].locate_mut();
    let &mut B = hlist![A, B, C].locate_mut();
    let &mut C = hlist![A, B, C].locate_mut();

    let (A, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    r1.is_known_to_be(B);
    r2.is_known_to_be(C);

    let (B, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    r1.is_known_to_be(A);
    r2.is_known_to_be(C);

    let (C, hlist_pat![r1, r2]) = hlist![A, B, C].pluck();
    r1.is_known_to_be(A);
    r2.is_known_to_be(B);

    // TODO: compile-fail
    // let &A = hlist![A, A].locate(); //~ ERROR type annotations required
    // TODO: compile-fail
    // let &A = hlist![B, C].locate(); //~ ERROR trait bound
}

#[test]
fn test_reuse_index() {
    use ::test_structs::unitlike_move::*;
    let abc = hlist![A, B, C];
    let mut def = hlist![D, E, F];

    def.at(abc.index_of::<A, _>()).is_known_to_be_ref(&D);
    def.at(abc.index_of::<B, _>()).is_known_to_be_ref(&E);
    def.at(abc.index_of::<C, _>()).is_known_to_be_ref(&F);
    def.at_mut(abc.index_of::<A, _>()).is_known_to_be_mut(&mut D);
    def.at_mut(abc.index_of::<B, _>()).is_known_to_be_mut(&mut E);
    def.at_mut(abc.index_of::<C, _>()).is_known_to_be_mut(&mut F);

    // TODO: compile-fail
    // let index = hlist![A, B, C].index_of::<A, _>();
    // def.at(abc.index_of::<A, _>()).is_known_to_be_ref(&E); //~ ERROR mismatched types
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

/// Newtype wrapper around an HList of indices that denotes a sequence of `pop_at` operations.
///
/// This is the only type that implements `IsSculptor`. The reason it exists is to make
/// it harder to confuse the representation of these lists for something else, by forcing
/// the words "pop seq" in front of you whenever you try to work directly with the indices
/// (the representation of which is not particularly useful for general purposes).
///
/// For an example of how this confusion could be troublesome,
/// consider the type `HList![A, B, C, D]`.
/// To sculpt the list `HList![C, B, A]`, the pop-sequence is `HList![P2, P1, P0]`.
/// To sculpt the list `HList![A, B, C]`, however, the pop-sequence is `HList![P0, P0, P0]`.
#[derive(Debug, Copy, Clone, Default)]
pub struct PopSeq<Idxs>(Idxs);

impl<Idxs> PopSeq<Idxs> {
    // NOTE: This name **does not** contain "pop seq" because it would stutter
    //       when written as `PopSeq::new(idxs)`.
    /// Construct from a sequence of PopAt indices.
    #[inline(always)]
    pub fn new(seq: Idxs) -> Self
    { PopSeq(seq) }

    // NOTE: This name **does** contain "pop seq" to serve as a reminder.
    /// Get the sequence of PopAt indices.
    #[inline(always)]
    pub fn pop_seq(self) -> Idxs
    { self.0 }
}

pub trait IsSculptor { }

// NOTE: This is a bit more permissive than desirable (we really only want
//       to accept lists of unary integers); but anything finer grained than
//       this seems to be prone to "overflow evaluating trait bound _: IsSculptor"
//       errors in some functions
impl<List: IsHList> IsSculptor for PopSeq<List> { }

//----------------------------------------------------------------------------

pub type TySculptRemainder<Ts, Is, List> = <List as Sculpt<Ts, Is>>::Remainder;
pub trait Sculpt<Targets, S: IsSculptor>: Sized + IsHList {
    type Remainder;

    fn sculpt(self) -> (Targets, Self::Remainder);

    fn static_sculptor() -> S;
}

pub type TySculptAt<S, List> = <List as SculptAt<S>>::Sculpted;
pub type TySculptAtRemainder<S, List> = <List as Sculpt<TySculptAt<S, List>, S>>::Remainder;
pub trait SculptAt<S: IsSculptor>: Sculpt<<Self as SculptAt<S>>::Sculpted, S> {
    type Sculpted;

    #[inline(always)]
    fn sculpt_at(self, _: S) -> (Self::Sculpted, Self::Remainder)
    { self.sculpt() }
}

impl<List: IsHList, T, Ts: IsHList, N: IsUnary, Ns: IsHList, Rem>
    Sculpt<HCons<T, Ts>, PopSeq<HCons<N, Ns>>> for List
where
    Self: Pluck<T, N, Remainder=Rem>,
    Rem: Sculpt<Ts, PopSeq<Ns>>,
{
    type Remainder = TySculptRemainder<Ts, PopSeq<Ns>, Rem>;

    #[inline(always)]
    fn sculpt(self) -> (HCons<T, Ts>, Self::Remainder) {
        let (t, remainder) = self.pluck();
        let (ts, remainder) = remainder.sculpt();
        (HCons(t, ts), remainder)
    }

    #[inline(always)]
    fn static_sculptor() -> PopSeq<HCons<N, Ns>>
    {
        let idx = <Self>::static_index();
        let PopSeq(idxs) = <PluckRemainderT<T, N, Self>>::static_sculptor();
        PopSeq(HCons(idx, idxs))
    }
}

impl<List: IsHList> Sculpt<HNil, PopSeq<HNil>> for List {
    type Remainder = Self;

    #[inline(always)]
    fn sculpt(self) -> (HNil, Self::Remainder)
    { (HNil, self) }

    #[inline(always)]
    fn static_sculptor() -> PopSeq<HNil>
    { PopSeq(HNil) }
}

impl<
    List: IsHList,
    Ts: IsHList,
    N: IsUnary, Ns: IsHList,
> SculptAt<PopSeq<HCons<N, Ns>>> for List
where
    Self: PopAt<N>,
    TyPopAtRemainder<N, Self>: SculptAt<PopSeq<Ns>, Sculpted=Ts>,
{
    type Sculpted = HCons<TyAt<N, Self>, Ts>;
}

impl<List: IsHList> SculptAt<PopSeq<HNil>> for List {
    type Sculpted = HNil;
}

#[test]
fn sculpt_nothing() {
    use ::test_structs::unitlike_move::{A, B};
    let (HNil, HNil) = HNil.sculpt();
    let (HNil, hlist_pat![A, B]) = hlist![A, B].sculpt();
    let (HNil, HNil) = HNil.sculpt_at(PopSeq(HNil));
    let (HNil, hlist_pat![A, B]) = hlist![A, B].sculpt_at(PopSeq(HNil));
}

#[test]
fn sculpt_at_doesnt_require_type_inference() {
    use ::test_structs::unitlike_move::{A, B, C, D, E};

    let abcde = hlist![A, B, C, D, E];
    let sculptor = abcde.sculptor_of::<HList![C, A, D], _>();

    let (hlist_pat![c, a, d], hlist_pat![b, e]) = abcde.sculpt_at(sculptor);
    a.is_known_to_be(A);
    b.is_known_to_be(B);
    c.is_known_to_be(C);
    d.is_known_to_be(D);
    e.is_known_to_be(E);
}
