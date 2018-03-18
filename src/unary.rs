//! Unary integers, to represent indices and lengths of lists.
//!
//! These are typelevel integers whose representation (in the type system)
//! can be thought of as just a bunch of tally lines:
//!
//! * `P0 = Zero`
//! * `P1 = Succ(Zero)`
//! * `P2 = Succ(Succ(Zero))`
//! * `P3 = Succ(Succ(Succ(Zero)))`
//! * `P4 = ...`
//!
//! It might seem like this is a really dumb representation for an integer,
//! and you're probably wondering why this crate doesn't just use `typenum`.
//! In fact, this is *the perfect representation* for working with `HList`;
//! far better than the binary representation used by `typenum`. After all,
//! it's *more or less* what you get when you replace all of the types in an
//! `HList` with `()`. (up to isomorphism).
//!
//! Two of the other `HList` crates sitting around call these `Here` and
//! `There` for some reason.  Beats me.

use ::std::ops::{Add, Sub};
use ::std::fmt;
use ::std::marker::PhantomData;

/// Unary integer zero.
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct Zero;

/// The unary integer `N + 1`.
///
/// The name comes from the "successor" function used in the Peano axioms.
/// This is in the hope that it might sound familiar to functional programmers,
/// and if not, then its name should at least stick!
///
/// This uses an opaque representation that unfortunately means you won't be
/// able to pattern match expressions like `let Succ(n) = m;`.
/// This is not a huge loss, as there is only one possible value for `n`;
/// you may construct it using `Default`.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Succ<N> {
    // We do not actually store N because it would create unnecessary codegen work:
    //
    // * Even though the methods should all optimize to noops, they
    //   need to be inlineable for this to actually occur.
    // * If they are inlineable, then this optimization will need to
    //   occur again and again at every callsite.
    //
    // At least, that's how I picture it happening.
    // Of course, HLists already have to deal with these same problems, and they
    // don't have an out. I have not personally seen the evidence that making this
    // optimization on peano integers really makes a notable difference to build
    // time, and if it turns out that it doesn't matter, we can backwards-compatibly
    // switch to the much nicer representation `pub struct Succ<N>(pub N)`.
    _marker: PhantomData<N>
}

impl<N> Default for Succ<N> {
    #[inline(always)]
    fn default() -> Self
    { Succ { _marker: PhantomData } }
}

pub trait IsUnary: Default {
    const VALUE: u32;

    #[inline(always)]
    fn succ(self) -> Succ<Self>
    { Default::default() }
}

impl<N: IsUnary> Succ<N> {
    #[inline(always)]
    pub fn pred(self) -> N
    { Default::default() }
}

impl IsUnary for Zero {
    const VALUE: u32 = 0;
}

impl<N: IsUnary> IsUnary for Succ<N> {
    const VALUE: u32 = 1 + N::VALUE;
}

impl fmt::Debug for Zero {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P0")
    }
}

impl<N: IsUnary> fmt::Debug for Succ<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P{}", <Self as IsUnary>::VALUE)
    }
}

pub mod consts {
    //! Constants (or rather, type aliases) for Peano integers.
    //!
    //! These are make-believe unit structs. Because there is
    //! both a type alias and a constant with the same name,
    //! you can use it in type and expression contexts alike.
    //!
    //! (one catch: you cannot use them in patterns currently
    //!  because PhantomData does not `#[derive(PartialEq, Eq)]`.
    //!  Either of RFCs )
    use super::*;

    macro_rules! gen_consts {
        ([$ThisTy:ty] [$ThisConst:expr] $ThisIdent:ident $($rest:ident)*)
        => {
            // FIXME test these links?

            /// Constant for a Peano integer.
            ///
            /// See the [constants](..) module for more information.
            pub type $ThisIdent = $ThisTy;

            /// Constant for a Peano integer.
            ///
            /// See the [constants](..) module for more information.
            pub const $ThisIdent : $ThisIdent = $ThisConst;

            gen_consts! {
                [Succ<$ThisTy>] [Succ { _marker: PhantomData }] $($rest)*
            }
        };

        ([$ThisTy:ty] [$ThisConst:expr])
        => {};
    }
    gen_consts!{
        [Zero] [Zero]
         P0  P1  P2  P3  P4  P5  P6  P7  P8  P9
        P10 P11 P12 P13 P14 P15 P16
    }
}

type AddT<A, B> = <A as Add<B>>::Output;
type SubT<A, B> = <A as Sub<B>>::Output;

impl Add<Zero> for Zero {
    type Output = Zero;

    #[inline(always)]
    fn add(self, _: Zero) -> Self::Output
    { Default::default() }
}

impl<N> Add<Succ<N>> for Zero {
    type Output = Succ<N>;

    #[inline(always)]
    fn add(self, _: Succ<N>) -> Self::Output
    { Default::default() }
}

// (note: this is the only way to write this that does not appear
//        to cause rustc to shit itself with infinite recursion)
impl<N: IsUnary, Rhs, S> Add<Rhs> for Succ<N>
where
    N: Add<Succ<Rhs>, Output=S>,
    S: IsUnary,
{
    type Output = AddT<N, Succ<Rhs>>;

    #[inline(always)]
    fn add(self, _: Rhs) -> Self::Output
    { Default::default() }
}

impl Sub<Zero> for Zero
{
    type Output = Zero;

    #[inline(always)]
    fn sub(self, _: Zero) -> Self::Output
    { Default::default() }
}

impl<N: IsUnary> Sub<Zero> for Succ<N>
{
    type Output = Succ<N>;

    #[inline(always)]
    fn sub(self, _: Zero) -> Self::Output
    { Default::default() }
}

impl<N: IsUnary, B: IsUnary, D> Sub<Succ<B>> for Succ<N>
where
    N: Sub<B, Output=D>,
    D: IsUnary,
{
    type Output = SubT<N, B>;

    #[inline(always)]
    fn sub(self, _: Succ<B>) -> Self::Output
    { Default::default() }
}

#[test]
fn test_unary_ops() {
    use self::consts::*;

    let _: P0 = P0 + P0;
    let _: P7 = P7 + P0;
    let _: P7 = P0 + P7;
    let _: P7 = P5 + P2;
    let _: P0 = P0 - P0;
    let _: P7 = P7 - P0;
    let _: P5 = P7 - P2;
}
