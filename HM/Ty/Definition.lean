
import Mathlib.Data.List.Basic

import LeanSubst
open LeanSubst

namespace HM

class FVs α where
  fvs : α -> List Nat

inductive Ty where
| var : Nat -> Ty
| arrow : Ty -> Ty -> Ty
| app : Ty -> Ty -> Ty
| const : String -> Ty

@[coe]
def Ty.from_action : Action Ty -> Ty
| .re y => .var y
| .su t => t

instance : Coe (Action Ty) Ty where
  coe := Ty.from_action

@[simp]
private def Ty.smap (σ : Subst Ty) : Ty -> Ty
| .var x => σ.act x
| .arrow x y => .arrow (smap σ x) (smap σ y)
| .const x => .const x
| .app x y  => .app (smap σ x) (smap σ y)


instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
private def fvs_ty : Ty -> List Nat
| .var x => [ x ]
| .arrow x y => fvs_ty x ∪ fvs_ty y
| .app x y => fvs_ty x ∪ fvs_ty y
| .const _ => {}

instance : FVs Ty where
  fvs := fvs_ty

/-
  How should a type scheme be defined?

  We want to represent quantified types, the ones that are quantified only in the outer level
  The inner type may refer to some global types

  In named representations we write them as

     σ := τ | ∀ α. σ

  where τ is a mono-type, meaning Typ from above (no quantifiers)
  and α is free in σ

  In DB representation we could just represent them
    as a pair of Nat and mono-type

    σ := (n, τ)

  where the variables from 0, n-1 free in τ, the rest (if they appear) are global and should not be substituted

-/
@[simp]
abbrev SchemeTy := List Nat × Ty

@[simp]
private def fvs_scheme : SchemeTy -> List Nat
| ⟨bvars, ty⟩ => fvs_ty ty \ bvars

instance : FVs SchemeTy where
  fvs := fvs_scheme


instance : FVs (List SchemeTy) where
  fvs Γ := Γ.foldr (fvs_scheme · ∪ ·) (init := [])

open FVs

#eval ([1, 2] ∪ [2,3]) \ [2]

def SchemeTy.instantiate : Nat -> SchemeTy -> (Nat × Ty)
| f, ⟨n, τ⟩ =>
  -- all the variables from 0 to  n-1 get mapped to f -> f + n-1
  -- and we return f + n
  let σ : Subst Ty := ⟨λ x => if x ∈ n then su (.var (x + f)) else su (.var x)⟩
  (f + n.length, τ[σ])

def Ty.generalize (Γ : List SchemeTy) (τ : Ty) : SchemeTy :=
  ⟨fvs τ \ fvs Γ, τ⟩

def unify' : Ty -> Ty -> Option (Subst Ty)
| .var x, t =>
  if x ∉ fvs t then
  return ⟨λ i => if i == x then su t else su (.var i)⟩
  else none
| .arrow t1 t2, .arrow p1 p2 | .app t1 t2, .app p1 p2 => do
  let σ1 <- unify' t1 p1
  let σ2 <- unify' t2 p2
  return σ1 ∘ σ2
| .const x, .const y => if x == y then return Subst.id Ty else none
| _, _ => none


end HM
