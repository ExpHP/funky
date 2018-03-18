## Associated type synonyms

### Naming

This crate uses a form of Hungarian notation for associated type synonyms;
`TySculptAt`, `TyAt`, etc.
Usually rust naming conventions shun this kind of notation, but I argue that the typical reasons do not apply here.
Normally, you can use modules to solve naming conflicts, but in this case, you will virtually always want the trait
in scope whenever the type is in scope.

`typenum` solves this by inventing a new name for every single operation;
`Prod` for `Mul::Output`, `Quot` for `Div::Output`.
I argue that this adds unnecessary cognitive overhead.

### Parameter order

#### Mechanically derived from trait

```rust
        <L as At<N>>::Value   -->  AtT<L, N>
<A as ZipWith<B, F>>::Output  -->  ZipWith<A, B, F>
```

* Nothing extra you need to learn.

#### Scalable ordering

```rust
        <L as At<N>>::Value   -->  AtT<N, L>
<A as ZipWith<B, F>>::Output  -->  ZipWith<B, F, A> ??
                              -->  ZipWith<F, A, B> ??
                              -->  ZipWith<F, B, A> ??
```

* Put `Self` last, since it is likely to be large.
  This scales better when writing large nested types.
* `ZipWith` shows how this can get confusing.
  `ZipWith<B, F, A>` would be most consistent,
  but for small A it looks bizarre and is easy to mess up.
  When A *is* large then it suddenly paradoxically becomes the easiest order
  to write, because you're just taking the chain of method calls and writing
  them in reverse.

## Traits as "type-level type annotations"

### Yes/No

#### With type-level types

```rust
pub trait At<Index: IsUnary>: IsHList {
    type Value;

    fn at(&self, index: Index) -> &Self::Value;

    fn at_mut(&mut self, index: Index) -> &mut Self::Value;
}
```

* (+) Presumably easier to debug type errors.
* (−) Makes it harder to extend the traits to other types.
    * e.g. implementing the traits on `&HCons`.  Do we really want
    `&HCons` to impl `IsHList`?  I think not.
* (+) No disadvantage to writing larger traits.


#### Without type-level types

```rust
pub trait At<Index> {
    type Value;

    fn at(&self, index: Index) -> &Self::Value;
}

pub trait AtMut<Index: IsUnary>: At<Index> {
    fn at_mut(&mut self, index: Index) -> &mut Self::Value;
}
```

* (+) Resolves the issue of extending the traits to other types.
* **Note:** Trait must be split up as shown to be the most effective.  
  This can be onerous.

### Naming

I also use a form of Hungarian for these; `IsSomething` to distinguish them
from both types (which they would otherwise resemble), and traits (which they
would otherwise get lost among in the docs).
That said, only these traits get reexported at the root,
so maybe the second point does not matter.

`Is` might not be the best prefix.
