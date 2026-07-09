# System FD

### Core

The `Core` folder contains everything related to the core language's metatheory

Specifically:

- Ty.lean: Syntax for Types
- Term.lean: Syntax for Terms
- Eval.lean: Term evaluator (Big step and small step)
- Infer.lean: Type Checker for Terms

- Reduction.lean : Specification for reduction
- Typing.lean: Specification of type checking

- Examples.lean : Example System FD programs from the paper
  - Sec. 2.1.1 Superclasses: Core.Examples.Boolean
  - Sec. 2.1 Open Data and Open Function: Core.Examples.Ordering
  - Sec. 2.2.1 Superclasses and Sec. 2.2.3 Default implementation and local instances: Core.Examples.Superclasses
  - Sec 2.2.2 Quantified superclasses: Core.Examples.AlternativeMonoid
  - Sec 2.3.1 Generalized superclasses and class aliases:  Core.Examples.ClassAlias
  - Sec. 2.3.2 Type Relationships: Core.Examples.MonadReaderRelation
  - Sec. 2.3.3 Type Relationships in context: Core.Examples.MonadReaderCtxRelation
  - Sec. 2.4 Open Functions and Coercions: Core.Examples.MonadReaderTypeFunction

This formalization proves:
- [x] Soundness of type checking with respect to type checking judgements: Core.Infer.TypeSound
- [x] Soundness of evaluation with respect to reduction semantics: Core.Eval.Soundness
- [x] Type Safety
  - [x] Progress: Core.Metatheory.Progress
  - [x] Preservation: Core.Metatheory.Preservation

### Build Instructions

- Ensure lean4 development environment is setup following the [standard approaches](https://lean-lang.org/install/).
- The development was checked with Lean v4.29.0

```
$ cd systemfd-lean
$ lake build
```

- The `lake build` command builds all the files from `Core`, `lean-subst`, `lilac` directories via `Main.lean` file
- The build command succeeds with the following output

```
ℹ [64/142] Replayed Core.Metatheory.Preservation
info: Core/Metatheory/Preservation.lean:408:0: 'Core.preservation_step' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [65/142] Replayed Core.Metatheory.Progress
info: Core/Metatheory/Progress.lean:426:0: 'Core.progress' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (142 jobs).
```
