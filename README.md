# It smells a bit `funky` in here...

This is (for now) just ExpHP's personal project reimplementing some of the ideas in `frunk`, attempting to explore the design space a bit more.

**This probably won't ever be published.** Instead, I hope to use what I learn here to contribute ideas to another similar project (probably [frunk](https://github.com/lloydmeta/frunk)?).

## Features

(**note:** examples are most likely broken by the time you read this)

### Reified indices, to improve ergonomics of working with multiple HLists in parallel

```rust
let list_a = hlist![A1, A2, A3];
let list_b = hlist![B1, B2, B3];

// Find the indices for sculpting
let sculptor = list_a.sculptor_of::<HList![A3, A1], _>();

// Apply them to both lists.
let (hlist_pat![A3, A1], hlist_pat![A2]) = list_a.sculpt_at(sculptor);
let (hlist_pat![B3, B1], hlist_pat![B2]) = list_b.sculpt_at(sculptor);

// Notice that the type of `list_b.sculpt_at(sculptor)` is always
// immediately known, without any help from type inference;
// the following does not produce a "Type annotations needed" error.
assert_eq!(list_b.sculpt_at(sculptor), list_b.sculpt_at(sculptor));
```

### Coproduct subsetting (`sculpt`) and supersetting (`embed`)

`sculpt` can turn `Coprod![A, B, C, D, E]` into `Either<Coprod![C, A, E]>, Coprod![B, D]>`.  
`embed` can turn `Coprod![C, A, E]` into `Coprod![A, B, C, D, E]`.

(actually wait a second, isn't `embed` just a special case of `sculpt` where the remainder is void?)  
(ehhhhhhh I'll do something about that later)

### Documentation that very profusely apologies about the index type parameters

Yes, the indices on the type-directed lookup methods *really do have to be type parameters.*

No, they can't be turned into associated types. *Try it, I dare you.*

## Usage

**Don't.**

If you just wanna try it out for kicks, you should use a git dependency with a `rev` tag: (this repo has no tags yet)

```toml
[dependencies]
funky = { rev = "777777777777", git = "https://github.com/ExpHP/funky" }
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Wait, what?! You want to contribute... *to this?!*

Well... alrighty, then.
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license,
shall be dual licensed as above, without any additional terms or conditions.
