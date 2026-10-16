import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

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

noncomputable def eqnsSize : List (Ty × Ty) -> Nat
| [] => 0
| .cons (t1, t2) eqns => 1 + t1.size + t2.size + eqnsSize eqns

noncomputable def UnifyState.eqnSize : UnifyState -> Nat
| ⟨_, eqns⟩ => eqnsSize eqns


def isVar : Core.Ty -> Bool
| t#_ => true
| _ => false

noncomputable def flipEqnsSize : List (Ty × Ty) -> Nat
| [] => 0
| .cons (t1, t2) es => if (¬ isVar t1) ∧ isVar t2 then 1 + flipEqnsSize es else flipEqnsSize es

noncomputable def UnifyState.flippedEqnSize : UnifyState -> Nat
| ⟨_, eqns⟩ => flipEqnsSize eqns

-- There is a triple we need to define as a termination measure
-- According to TRAAT
-- n1 = number of variables that are not in solved form
-- n2 = size of S i.e. eqnSize above
-- n3 = number of equations of the form (t = x) in S

def freeVars : Ty -> Finset Nat
| t#x => {x}
| .app t1 t2 | .arrow t1 t2 | .eq _ t1 t2 => freeVars t1 ∪ freeVars t2
| _ => {}


noncomputable def UnifyStateSize (u : UnifyState) : Nat × Nat × Nat := ⟨0, u.eqnSize, u.flippedEqnSize⟩

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
