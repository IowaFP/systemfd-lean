
# System FD

# Plan:

## Closed Datatypes

Generalize to multimatches with proper binders:
(Allow wildcard patterns?)

```
match a, b with
| Just x, Just y => t1
| Just x, Nothing => t2
| Nothing, _ => t3
```

The first pattern is of type `Vec n (Vec m (String x Nat) x Term)`
(we don't need an inner `Vec`, but the scrutinees will force a Vec, so why not reuse the `m`)

To determine if the match is exhaustive and unique, we can build an `m`-cube:
Every case marks the relative part of the `m`-cube that has been tracked
If at any point a position is double-marked then it is not unique
If at any point a position is not marked then the match is not exhaustive

reduction is via proper lifts, so a constructor `branch left right`
is equivalent to `branch 2` and when the case is taken:

```
match (branch t1 t2) with
| leaf 0 => c1
| branch 2 => c2
```

then this reduces to `c1[σ]` where `σ = su t1 :: su t2 :: +0`
(or rather `σ = [su t1, su t2] ++ +0`)
i.e., a generalized beta substitution

## Open Datatypes

!!Guard is removed!!

instances for open methods are treated as pattern match cases (just like closed data types)

open methods are fully applied always? (I think yes, treat them like a match expression)

if a match is exhaustive and unique, then you can't produce a + or a 0

## Termination Predicate

Add a parameter to the typing/globalwf judgement that characterizes a termination condition

Later on we can pick one and show erasure relative to that




















The project is divided into 2 main directories

### SystemFD

This folder contains everything related to the core language's metatheory
Specifically:

- Term.lean: Terms of the core language
- Evaluator.lean: evaluates terms
- Algorithm.lean: typecheck terms

- Reduction.lean : Specification for reduction
- Judgment.lean: Specification of type checking

- Examples.lean : Example System FD programs

This formalization proves:
- [x] Soundness of type checking with respect to type checking judgements
- [x] Soundness of evaluation with respect to reduction semantics
- [x] Progress and preservation


### Hs

This folder contains everything related to the surface syntax and its elaboration into the core languate
Specifically:

- HsTerm.lean : Terms to encode (an approximation of) the surface level language
- Algorithm.lean : Type directed compilation/elaboration of a surface level term to a core term
- SynthInstance.lean : Synthesis of coercions and instances

- Examples.lean : Example System FD programs

### Building Instructions

- Ensure lean4 development environment is setup following the [standard approaches](https://lean-lang.org/install/).

```
$ cd systemfd-lean
$ lake build
```

- The `lake build` command builds all the files from `Hs` and `SystemFD` directories via `Main.lean` file


- [ ] Examples, Booleans, Nats, Fundep examples, Injective and Maybe
- [ ] Type inference
- [ ] Evaluator
- [ ] Type inference sound
- [ ] Evaluator sound
