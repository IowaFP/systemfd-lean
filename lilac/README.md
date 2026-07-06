# lilac

Lilac is a data structure library for Lean where data is built using function encodings and related to some other sensible type.
Hence, the functional encoding of a vector of `A`s is `Fun.Vec A n = Fin n -> A`, and it is related to a standard inductive definition.

## Motivation

Lean is restrictive in what kinds of types are allowed to appear in inductive data.
For example, the following datatype is allowed, but is translated to a mutual-inductive:
```lean
inductive Ex where
| base : Ex
| stuff : List Ex -> Ex
```
This is workable, but annoying.
When you want to generate automatic procedures that induct on `Ex` you run into problems.
Instead, we could do something like this:
```lean
inductive Ex where
| base : Ex
| stuff n : Fun.Vec Ex n -> Ex
```
Where `Fun.Vec` is the functional encoding of vectors that is related to the inductive `Vec`.
This is no longer a mutual-inductive type.

## Problems

Since we're cheating the nested inductive data issue one may wonder what price we pay for our devil's bargain.
There are unfortunately some prices to pay:

### No Encapsulation

We can't really treat our datatypes as encapsulated, Lean has to know that `Fun.Vec A n` really is `Fin n -> A`.
This is particularly annoying when two encodings are morally "the same" such as `Fun.Vec T n`, and a heterogenous variant `Fun.Hec V n`.
The nil constructors for both are "the same" and this can cause loops in `simp` if we're not careful.
It also means that definition of all functional encodings must be exposed.
To mitigate these issues a "companion" type is provided (e.g., `Fun.Vec` has a companion `Vec`) with the idea that a development would escape into `Vec` as soon as possible.

### Recursion is Finicky

If a size function over `Ex` were impossible then this approach would be dead in the water.
Such a function is possible:
```lean
def Ex.size : Ex -> Nat
| base => 0
| stuff vs =>
  let sizes : Fun.Vec _ _ := size <$> vs
  Vec.sum sizes.to + 1
```
However, we must map over the container data using a macro `<$>` and must record the output in a variable at the correct type.
Otherwise, Lean will obliterate the type information (treating it instead as a `Fin n -> A`) and not know what to do with itself.
