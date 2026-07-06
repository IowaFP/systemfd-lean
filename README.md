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

- Examples.lean : Example System FD programs

This formalization proves:
- [x] Soundness of type checking with respect to type checking judgements
- [x] Soundness of evaluation with respect to reduction semantics
- [x] Type Safety
  - [x] Progress
  - [x] Preservation

### Building Instructions

- Ensure lean4 development environment is setup following the [standard approaches](https://lean-lang.org/install/).

```
$ cd systemfd-lean
$ lake build
```

- The `lake build` command builds all the files from `Core`, `lean-subst`, `lilac` directories via `Main.lean` file
