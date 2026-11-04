
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
| tpl : Fun.Vec Term n → Term
-- | prj : (n : Nat) → Fun.Vec Term n → Term
-- Number of cases: n
-- Input : i
-- Guard: i = n: go to case i
| switch : (n : Nat) → Fun.Vec Term n → (i : Fin n) → Term

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| var x => var (r.act x)
| defn x => defn x
| app t1 t2 => app (rmap r t1) (rmap r t2)
| lam t => lam (rmap r.lift t)
| tpl v => tpl (rmap r <$> v)
-- | prj n v => prj n (rmap r <$> v)
--| pair t1 t2 => pair (rmap r.lift t1) (rmap r.lift t2)
-- | fst t => fst (rmap r t)
--| snd t => snd (rmap r t)
| switch n v i => switch n (rmap r <$> v) i

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
| tpl v => tpl (smap σ <$> v)
-- | prj n v => prj n (smap σ <$> v)
-- | pair t1 t2 => pair (smap σ t1) (smap σ t2)
-- | fst t => fst (smap σ t)
-- | snd t => snd (smap σ t)
| switch n v i => switch n (smap σ <$> v) i

instance : SubstMap Term Term where
  smap := Term.smap

abbrev GlobalEnv := List Term

-- TODO: add erased context here
inductive Red (G : GlobalEnv) : Term -> Term -> Prop where
| beta : Red G (.app (.lam b) t) b[su t::+0σ]
| defn : G[x]? = some t -> Red G (.var x) t
-- | fst : Red G (.fst (.pair t₁ t₂)) t₁
-- | snd : Red G (.fst (.pair t₁ t₂)) t₂
| switch : Red G (.switch n v i) (v i)

notation:160 G:160 " ⊢ " t:160 " ~>' " t':160 => Red G t t'

inductive RedOpt (G : GlobalEnv) : Term → Term → Prop
  | refl : RedOpt G x x
  | step :  Red G x y → RedOpt G x y

notation:160 G:160 " ⊢ " t:160 " ~>'? " t':160 => Red G t t'

inductive RedStar (G : GlobalEnv) : Term → Term → Prop
  | refl : RedStar G x x
  | step : Red G x y → Red G y z → RedStar G x z

notation:160 G:160 " ⊢ " t:160 " ~>'* " t':160 => Red G t t'

inductive RedPlus (G : GlobalEnv) : Term → Term → Prop where
  | one : Red G x y → RedPlus G x y
  | step : Red G x y → Red G y z → RedPlus G x z

notation:160 G:160 " ⊢ " t:160 " ~>'+ " t':160 => Red G t t'

end Untyped

/--
Erases both types and coercions.
-/
def Term.erase : Term → Untyped.Term
  | var n => .var n
  -- Just like a variable
  | defn x => .defn x
  -- Special constructors
  | spctor _ _ _ _ _ => sorry
  | ctor0 (.refl _) => .lam (.var 0)
  | ctor1 (.prj n) t => sorry
  | ctor1 (.appt _) t => t.erase
  | ctor2 v t1 t2 => sorry
  | tbind _ _ t => t.erase
  | lam _ t => .lam t.erase
  | cast _ t1 t2 => t2.erase
  -- create an outer switch of m cases
  -- and each one is a switch of n cases
  | mtch m n vm pmn vn => sorry

deriving instance BEq for Global

def GlobalEnv_erase (G : GlobalEnv) : Untyped.GlobalEnv := sorry
  -- G.map Term.erase

-- TODO: add erased contexts

notation "⟦" e "⟧" => Term.erase e
notation "⟦" G "⟧" => GlobalEnv_erase G

-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily many steps at the top
-- -- TODO: explore bisimulations
def erasure (wf : ⊢ G)(oe : OpenExhaustive G)(t t' : Term) :
  G ⊢ t ~> t' → ⟦G⟧ ⊢ ⟦t⟧ ~>'? ⟦t'⟧ := by sorry
