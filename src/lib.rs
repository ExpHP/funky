
#[macro_use]

mod macros;

pub use self::hlist::{IsHList, HNil, HCons};
pub mod hlist;

pub use self::unary::{IsUnary, Zero, Succ};
pub mod unary;

pub(crate) mod test_structs;
