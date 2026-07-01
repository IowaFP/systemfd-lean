import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Util
import Core.Vec

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Metatheory.Closed

open Lilac
open LeanSubst

namespace Core

theorem Kinding.unique
  : G&Δ ⊢ A : K -> G&Δ ⊢ A : L -> K = L
:= sorry

theorem PatternBinders.unique
  : PatternBinders v G Δ m S1 p ζ1 ξ1 ->
    PatternBinders v G Δ m S2 p ζ2 ξ2 ->
    S1 = S2 ->
    ζ1 = ζ2 ∧ ξ1 = ξ2
:= sorry

theorem CoercionProject.unique
  : CoercionProject G Δ n T1 A ->
    CoercionProject G Δ n T2 B ->
    T1 = T2 ->
    A = B
:= sorry

theorem Typing.unique
  : G&Δ,Γ ⊢ t : A -> G&Δ,Γ ⊢ t : B -> A = B
| var j1 j2, var j1' j2' => by
  rw [j1] at j1'; cases j1'; rfl
| defn j1 j2, defn j1' j2' => by
  rw [j1] at j1'; cases j1'; rfl
| spctor j1 e1 e2 j2 j3 j4 j5 j6 j7 , spctor j1' e1' e2' j2' j3' j4' j5' j6' j7' => by
  rw [j1] at j1'; cases j1'; subst e2 e2'; rfl
| mtch (S := S) (ζ := ζ) j1 j2 j3 j4 j5, mtch (S := S') j1' j2' j3' j4' j5' =>
  have lem1 := λ i => unique (j1 i) (j1' i)
  have lem2 : S.to = S'.to := Vec.ext_get (by simp [Vec.get_to]; exact lem1)
  have lem3 := PatternBinders.unique (j3 0) (j3' 0) lem2
  have lem4 := unique (B := B⟨Ren.add Ty (ζ 0).length⟩) (j4 0) (j4' 0 ▸ simp [lem3])
  have lem5 : A⟨Ren.add Ty (ζ 0).length⟩⟨Ren.sub Ty (ζ 0).length⟩
    = B⟨Ren.add Ty (ζ 0).length⟩⟨Ren.sub Ty (ζ 0).length⟩ := by rw [lem4]
  by simp at lem5; exact lem5
| lam j1 j2, lam j1' j2' =>
  have lem := unique j2 j2'
  by simp [lem]
| app j1 j2, app j1' j2' =>
  have lem := unique j1 j1'
  by cases lem; rfl
| lamt j1 j2, lamt j1' j2' =>
  have lem := unique j2 j2'
  by simp [lem]
| appt j1 j2 e, appt j1' j2' e' =>
  have lem := unique j1 j1'
  by cases lem; simp [e, e']
| refl j1, refl j1' =>
  have lem := Kinding.unique j1 j1'
  by simp [lem]
| cast j1 j2 j3 e, cast j1' j2' j3' e' =>
  have lem1 := unique j2 j2'
  have lem2 := unique j3 j3'
  by cases lem1; simp [e, e']
| prj j1 j2, prj j1' j2' =>
  have lem1 := unique j1 j1'
  CoercionProject.unique j2 j2' lem1
| allc j1, allc j1' =>
  have lem := unique j1 j1'
  by cases lem; rfl
| apptc j1 j2 e1 e2, apptc j1' j2' e1' e2' =>
  have lem1 := unique j1 j1'
  have lem2 := unique j2 j2'
  by cases lem1; cases lem2; simp [e1, e2, e1', e2']

namespace Core
