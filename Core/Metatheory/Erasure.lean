
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
-- Parameter: n
-- Inputs: i
-- Guard: i = n: Case 1; Case 2
| ite : Nat → Nat → Term → Term → Term

inductive Red : Term -> Term -> Prop where
-- TODO: use LeanSubst in beta
| beta : Red (.lam t) sorry
| fst : Red (.fst (.pair t₁ t₂)) t₁
| snd : Red (.fst (.pair t₂ t₂)) t₂
-- TODO: maybe break up into ite_true, ite_false?
| ite : Red ((.ite n i t₁ t₂)) (if i = n then t₁ else t₂)

inductive RedStar : Term → Term → Prop where
  | refl : RedStar x x
  | step : Red x y → Red y z → RedStar x z

inductive RedPlus : Term → Term → Prop where
  | refl : Red x y → RedPlus x y
  | step : Red x y → Red y z → RedPlus x z

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
