
-- TODO: maybe describe the target language
-- as a separate type.

import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing

namespace Core

/--
Erases both types and coercions.
-/
def Term.erase (G : GlobalEnv): Term → Term
  | var n => var n
  -- TODO: determine how to
  -- handle case where def is none.
  | defn x => 
    match lookup_defn G x with
      | some (A, t) => t
      -- FIXME: remove var 0
      | none => var 0
  | _ => sorry

notation "⟦" e "⟧_[" G "]" => Term.erase G e

-- TODO: explore bisimulations
def erasure (G : GlobalEnv)(t t' : Term) :
  G ⊢ t ~> t'
  → ⟦t⟧_[G] = ⟦t'⟧_[G] ∨ G ⊢ ⟦t⟧_[G] ~> ⟦t'⟧_[G] := by sorry
