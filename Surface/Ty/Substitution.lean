import LeanSubst
import Surface.Ty.Definition

open LeanSubst


@[coe]
def Surface.Ty.from_action : Subst.Action Surface.Ty -> Surface.Ty
| .re y => t`#y
| .su t => t

@[simp]
theorem Surface.Ty.from_action_id {n} : from_action (+0 n) = t`#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Surface.Ty.from_action_succ {n} : from_action (+1 n) = t`#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Surface.Ty.from_acton_re {n} : from_action (re n) = t`#n := by simp [from_action]

@[simp]
theorem Surface.Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance Surface.Coe_ActionTyTy : Coe (Subst.Action Surface.Ty) Surface.Ty where
  coe := Surface.Ty.from_action

@[simp]
def Surface.Ty.rmap (r : Ren) : Ty -> Ty
| t`#x => t`#(r x)
| gt`#x => gt`#x
| A `-:> B => rmap r A `-:> rmap r B
| `∀[K] P => `∀[K] rmap r.lift P
| app f a => rmap r f `• rmap r a

instance Surface.instRenMap_SurfaceTy : RenMap Surface.Ty where
  rmap := Surface.Ty.rmap

@[simp]
def Surface.Ty.smap (σ : Subst Surface.Ty) : Surface.Ty -> Surface.Ty
| t`#x => σ x
| gt`#x => gt`#x
| A `-:> B => smap σ A `-:> smap σ B
| `∀[K] P => `∀[K] smap σ.lift P
| app f a => smap σ f `• smap σ a

instance Surface.instSubstMap_TyTy : SubstMap Surface.Ty Surface.Ty where
  smap := Surface.Ty.smap

@[simp]
theorem Surface.Ty.subst_var : (t`#x)[σ:Ty] = σ x := by
  simp [SubstMap.smap]

@[simp]
theorem Surface.Ty.subst_global : (gt`#x)[σ:Ty] = gt`#x := by
  simp [SubstMap.smap]

@[simp]
theorem Surface.Ty.subst_arr {A B : Ty} : (A `-:> B)[σ:Ty] = A[σ:_] `-:> B[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Surface.Ty.subst_all : (`∀[K] P)[σ:Ty] = `∀[K] P[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Surface.Ty.subst_app : (f `• a)[σ:Ty] = f[σ:_] `• a[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Surface.Ty.from_action_compose {x} {σ τ : Subst Ty}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Ty.from_action]

theorem Surface.Ty.apply_id {t : Surface.Ty} : t[+0] = t := by
  induction t; all_goals (simp at *; try simp [*])

instance Surface.instSubstMapId_TyTy: SubstMapId Surface.Ty Surface.Ty where
  apply_id := Surface.Ty.apply_id

theorem Surface.Ty.apply_stable (r : Ren) (σ : Subst Surface.Ty)
  : r.to = σ -> rmap r = smap σ
:= by subst_solve_stable r, σ

instance Surface.instSubstMapStable_Ty: SubstMapStable Surface.Ty where
  apply_stable := Surface.Ty.apply_stable

theorem Surface.Ty.apply_compose {s : Ty} {σ τ : Subst Ty} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Ty, s, σ, τ

instance Surface.instSubstMapCompose_TyTy : SubstMapCompose Surface.Ty Surface.Ty where
  apply_compose := Surface.Ty.apply_compose

theorem Surface.Ty.rename_preserves_var_shape {r : Ren} : t`#x = T[r] -> ∃ y,  (T = t`#y ∧ x = r y) := by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h; assumption


theorem Surface.Ty.rename_preserves_global_shape {r : Ren} : gt`#x = T[r] -> T = gt`#x := by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case global => symm at h; assumption


theorem Surface.Ty.rename_preserves_arrow_shape {A B : Ty}{r : Ren} : A `-:> B = T[r] ->
  (∃ A' B' : Ty, (T = A' `-:> B') ∧  A = A'[r] ∧ B = B'[r])
:= by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case arrow a1 a2 _ _ => exists a1; exists a2

theorem Surface.Ty.rename_preserves_app_shape {A B : Ty}{r : Ren} : (A `• B) = T[r] ->
  (∃ A' B' : Ty, (T = A' `• B') ∧  A = A'[r] ∧ B = B'[r])
:= by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case app a1 a2 _ _  =>
  cases h.1; cases h.2; clear h
  exists a1; exists a2


theorem Surface.Ty.rename_preserves_all_shape {P : Ty}{r : Ren} : (`∀[K] P) = T[r] ->
  (∃ P' : Ty, (T = `∀[K]P') ∧  P = P'[re 0::↑r ∘ +1:Ty])
:= by
intro h
induction T generalizing K P <;> simp at *
case var => simp [Ren.to] at h
case all a ih =>
  cases h.1; cases h.2; clear h
  exists a;
