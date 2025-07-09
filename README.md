
# System FD

The project is divided into 2 main directories

### SystemFD

This folder inhabits everything related to the core language's metatheory
Specifically:

- Term.lean: Terms of the core language
- Evaluator.lean: evaluates terms
- Algorithm.lean: typecheck terms

- Reduction.lean : Specification for reduction
- Judgment.lean: Specification of type checking


This formalization proves:
- [x] Soundness of type checking with respect to type checking judgements
- [x] Soundness of evaluation with respect to reduction semantics
- [x] Progress and preservation


### Hs

This folder inhabits everything related to the surface syntax and its elaboration into the core languate
Specifically:

- HsTerm.lean : Terms to encode (an approximation of) the surface level language
- Algorithm.lean : Type directed compilation/elaboration of a surface level term to a core term
- SynthInstance.lean : Synthesis of coercions and instances
