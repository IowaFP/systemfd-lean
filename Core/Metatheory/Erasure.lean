
-- TODO: maybe describe the target language
-- as a separate type.

import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing

open Lilac
open LeanSubst
open List

namespace Core

namespace Untyped

/-- A term in the untyped target language. -/
inductive Term
| var : Nat → Term
| defn : String → Term
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
| defn x => defn x
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
| defn x => defn x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| lam t => lam (smap σ.lift t)
| pair t1 t2 => pair (smap σ t1) (smap σ t2)
| fst t => fst (smap σ t)
| snd t => snd (smap σ t)
| switch n i v => switch n i (smap σ <$> v)

instance : SubstMap Term Term where
  smap := Term.smap

abbrev GlobalEnv := List Term

-- TODO: add erased context here
inductive Red (G : GlobalEnv) : Term -> Term -> Prop where
-- TODO: use LeanSubst in beta
| beta : Red G (.app (.lam b) t) b[su t::+0σ]
| defn :
  G[x]? = some t -> Red G (.var x) t
| fst : Red G (.fst (.pair t₁ t₂)) t₁
| snd : Red G (.fst (.pair t₁ t₂)) t₂
| switch : Red G (.switch n i v) (v i)


inductive RedStar (G : GlobalEnv) : Term → Term → Prop
  | refl : RedStar G x x
  | step : Red G x y → Red G y z → RedStar G x z

inductive RedPlus (G : GlobalEnv) : Term → Term → Prop where
  | one : Red G x y → RedPlus G x y
  | step : Red G x y → Red G y z → RedPlus G x z

end Untyped

/--
Erases both types and coercions.
-/
def Term.erase : Term → Untyped.Term
  | var n => .var n
  -- Just like a variable
  | defn x => .defn x
  | _ => sorry

-- TODO: add erased contexts

notation "⟦" e "⟧" => Term.erase e

-- -- TODO: explore bisimulations
-- def erasure (wf : ⊢ G)(oe : OpenExhaustive G)(t t' : Term) :
--   G ⊢ t ~> t'
--   → ⟦t⟧ = ⟦t'⟧ ∨ [G] ⊢ ⟦t⟧ ~>' ⟦t'⟧ := by sorry
