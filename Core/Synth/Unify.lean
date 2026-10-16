import Core.Ty.Definition
import Core.Ty.Substitution
import Core.Ty.Structure

import Core.Typing

import LeanSubst
import Lilac

-- open Lilac
open LeanSubst

namespace LeanSubst

def Subst.Dom (σ : Subst Core.Ty) := ∀ i, Core.Ty.from_action (σ.act i) ≠ t#i

end LeanSubst

namespace Core.Ty

/-- heavily inspired by https://github.com/codyroux/traat-lean/tree/main/Traat -/

-- σ is a unifier for t and u if t[σ] = u[σ]
def Unifier (σ : Subst Ty) (t u : Core.Ty) : Prop := t[σ] = u[σ]
def Unify (t u : Core.Ty) := ∃ σ : Subst Ty, t[σ] = u[σ]

-- what about most general unifier?

--
-- Proving termination for this is going to be very annoying
partial def unify' : (t u : Ty) -> Option (Subst Ty)
| .var x, t => return ⟨λ y => if x == y then su t else su t#x⟩
| .global x, .global y => if x == y then return Subst.id Ty else none
| .arrow x1 y1, .arrow x2 y2 | .app x1 y1, .app x2 y2 => do
  let σ1 <- unify' x1 y1
  let σ2 <- unify' x2 y2
  return σ1 ∘ σ2
| .eq k1 x1 y1, .eq k2 x2 y2 =>
  if k1 == k2 then do
  let σ1 <- unify' x1 y1
  let σ2 <- unify' x2 y2
  return σ1 ∘ σ2
  else none
| _, _ => none


/-- Contains 2 things, the unprocessed equalties, and the coercion itself -/
structure UnifyState where
  subst : Subst Core.Ty
  equations : List (Ty × Ty)

def UnifyState.id : UnifyState := ⟨Subst.id Ty, []⟩

def eqnSize : List (Ty × Ty) -> Nat
| [] => 0
| .cons (t1, t2) eqns => 1 + t1.size + t2.size + eqnSize eqns

def UnifyState.size : UnifyState -> Nat
| ⟨_, eqns⟩ => eqnSize eqns


-- Performs one step of unification
def unifyStep (u : UnifyState) : Option UnifyState :=
  match u.equations with
  | [] => none
  | .cons (t#x, t) eqs =>
    let τ : Subst Ty := ⟨λ y => if x == y then .su t else .su t#y⟩
    return ⟨u.subst ∘ τ, eqs⟩
  | .cons (t, t#x) eqs => return ⟨u.subst, (t#x, t) :: eqs⟩
  | .cons (gt#x, gt#y) eqs => if x == y then return ⟨u.subst, eqs⟩ else none
  | .cons (.arrow x1 y1, .arrow x2 y2) eqs
  | .cons (.app x1 y1, .app x2 y2) eqs =>
    return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩
  | .cons (.eq k1 x1 y1, .eq k2 x2 y2) eqs =>
    if k1 == k2 then return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩ else none
  | _ => none




theorem unify_soundness {t u : Ty} {σ  : Subst Ty} : unify' t u = some σ -> Unifier σ t u := by sorry

theorem unify_completeness {t u : Ty} {σ  : Subst Ty} : Unifier σ t u -> unify' t u = some σ := by sorry


theorem unify_correctness : unify' t u = some σ ↔ Unifier σ t u := ⟨unify_soundness, unify_completeness⟩

-- what about well kindedness?
-- we may want to have something like:
-- G,Δ ⊢ σ = ∀ i, ∃ k, G,Δ ⊢ (σ.act i).from_action : K
--

end Core.Ty
