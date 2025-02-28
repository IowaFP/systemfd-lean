# SystemFD

## Overview

This development formalizes the metatheory of System FD in Lean4, specifically:
- Progress, and
- Preservation

The following files are revelant to the development:

- SystemFD.Term.Definition: Terms of the language
- SystemFD.Evaulator: evaluates terms
- SystemFD.Algoritm: typecheck terms

- SystemFD.Reduction : Term reduction specification
- SystemFD.Judgement: Typing judgment specification

- SystemFD.Metatheory.Progress : States the Progress lemma
- SystemFD.Metatheory.Preservation: States and proves the Preservation lemma

- SystemFD.Examples : Contains all the examples from the paper submission along with some extra ones

## Building instructions

[VSCode](https://lean-lang.org/lean4/doc/quickstart.html) or [Emacs](https://github.com/leanprover-community/lean4-mode)

```lean4
$ cd systemfd-lean
$ lake build
```

This development has been tested on `lean4:4.15.0`
