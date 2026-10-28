
-- TODO: maybe describe the target language
-- as a separate type.

import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing

namespace Core

namespace Untyped

/-- A term in the untyped target language. -/
inductive Term
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term
-- Tuples
| pair : Term → Term → Term
| fst : Term → Term
| snd : Term → Term
-- Guard: Case 1; Case 2
| ite : Bool → Term → Term → Term

-- TODO: define reductions.

end Untyped

/--
Erases both types and coercions.
-/
def Term.erase {G : GlobalEnv} (wf : ⊢ G): Term → Untyped.Term
  | var n => .var n
  -- TODO: determine how to
  -- handle case where def is none.
  | defn x => 
    match lookup_defn G x with
      | some (A, t) => sorry -- Term.erase wf t
      | none => sorry
  | _ => sorry

notation "⟦" e "⟧_[" G "]" => Term.erase G e

-- -- TODO: explore bisimulations
-- def erasure (G : GlobalEnv)(t t' : Term) :
--   G ⊢ t ~> t'
--   → ⟦t⟧_[G] = ⟦t'⟧_[G] ∨ G ⊢ ⟦t⟧_[G] ~> ⟦t'⟧_[G] := by sorry
