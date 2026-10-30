
-- TODO: maybe describe the target language
-- as a separate type.

import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing

open Lilac
open LeanSubst

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
-- Number of cases: n
-- Input : i
-- Guard: i = n: go to case i
| switch : (n : Nat) → (i : Fin n) → Fun.Vec Term n → Term


@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| var x => var (r.act x)
| app t1 t2 => app (rmap r t1) (rmap r t2)
| lam t => lam (rmap r.lift t)
| pair t1 t2 => pair (rmap r.lift t1) (rmap r.lift t2)
| fst t => fst (rmap r t)
| snd t => snd (rmap r t)
| switch n i v => switch n i (rmap r <$> v)

instance : RenMap Term Term where
  rmap := Term.rmap

@[coe]
def Term.from_action : Action Term -> Term
| .re y => var y
| .su t => t

instance : Coe (Action Term) Term where
  coe := Term.from_action

def Term.smap (σ : Subst Term) : Term → Term
| var x => σ.act x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| lam t => lam (smap σ.lift t)
| pair t1 t2 => pair (smap σ t1) (smap σ t2)
| fst t => fst (smap σ t)
| snd t => snd (smap σ t)
| switch n i v => switch n i (smap σ <$> v)

instance : SubstMap Term Term where
  smap := Term.smap

inductive Red : Term -> Term -> Prop where
-- TODO: use LeanSubst in beta
| beta : Red (.app (.lam b) t) b[su t::+0σ]
| fst : Red (.fst (.pair t₁ t₂)) t₁
| snd : Red (.fst (.pair t₁ t₂)) t₂
| switch : Red (.switch n i v) (v i)

inductive RedStar : Term → Term → Prop
  | refl : RedStar x x
  | step : Red x y → Red y z → RedStar x z

inductive RedPlus : Term → Term → Prop where
  | one : Red x y → RedPlus x y
  | step : Red x y → Red y z → RedPlus x z

end Untyped

/--
Erases both types and coercions.
-/
def Term.erase {G : GlobalEnv} (wf : ⊢ G): Term → Untyped.Term
  | var n => .var n
  -- Just like a variable
  | defn x => sorry
  | _ => sorry

notation "⟦" e "⟧_[" G "]" => Term.erase G e

-- -- TODO: explore bisimulations
-- def erasure (G : GlobalEnv)(t t' : Term) :
--   G ⊢ t ~> t'
--   → ⟦t⟧_[G] = ⟦t'⟧_[G] ∨ G ⊢ ⟦t⟧_[G] ~> ⟦t'⟧_[G] := by sorry
