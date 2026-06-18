import Core.Vec
import Core.Util
import Core.Ty.Definition

open Lilac
open LeanSubst

namespace Core

@[coe]
def Ty.from_action : Action Ty -> Ty
| .re y => t#y
| .su t => t

@[simp]
theorem Ty.from_action_id {n} : from_action (+0σ.act n) = t#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Ty.from_action_succ {n} : from_action (+1σ.act n) = t#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Ty.from_acton_re {n} : from_action (re n) = t#n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (r : Ren Ty) : Ty -> Ty
| t#x => t#(r.act x)
| gt#x => gt#x
| A -:> B => rmap r A -:> rmap r B
| ∀[K] P => ∀[K] rmap (r.lift) P
| app f a => rmap r f • rmap r a
| A ~[K]~ B => rmap r A ~[K]~ rmap r B

instance : RenMap Ty Ty where
  rmap := Ty.rmap

@[simp]
theorem Ty.ren_var {r : Ren Ty} : (t#x)⟨r⟩ = t#(r.act x) := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.ren_global {r : Ren Ty} : (gt#x)⟨r⟩ = gt#x := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.ren_arr {A B : Ty} {r : Ren Ty} : (A -:> B)⟨r⟩ = A⟨r⟩ -:> B⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.ren_all {r : Ren Ty} : (∀[K] P)⟨r⟩ = ∀[K] P⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.ren_app {r : Ren Ty} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.ren_eq {r : Ren Ty} : (A ~[K]~ B)⟨r⟩ = A⟨r⟩ ~[K]~ B⟨r⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Ty Ty where
  apply_id := by subst_solve_id

instance : RenMapCompose Ty Ty where
  apply_compose := by subst_solve_compose

@[simp]
def Ty.smap (σ : Subst Ty) : Ty -> Ty
| t#x => σ.act x
| gt#x => gt#x
| A -:> B => smap σ A -:> smap σ B
| ∀[K] P => ∀[K] smap σ.lift P
| app f a => smap σ f • smap σ a
| A ~[K]~ B => smap σ A ~[K]~ smap σ B

instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
theorem Ty.subst_var {σ : Subst Ty} : (t#x)[σ] = σ.act x := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_global {σ : Subst Ty} : (gt#x)[σ] = gt#x := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_arr {σ : Subst Ty} {A B : Ty} : (A -:> B)[σ] = A[σ] -:> B[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_all {σ : Subst Ty} : (∀[K] P)[σ] = ∀[K] P[σ.lift] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_app {σ : Subst Ty} : (f • a)[σ] = f[σ] • a[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_eq {σ : Subst Ty} : (A ~[K]~ B)[σ] = A[σ] ~[K]~ B[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_compose {x : Nat} {σ τ : Subst Ty}
  : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ.act x = z
  cases z <;> simp [Ty.from_action]

@[simp]
theorem Ty.from_action_compose_ren {x : Nat} {σ : Subst Ty} {r : Ren Ty}
  : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
:= by
  simp [Ty.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

instance : SubstMapId Ty Ty where
  apply_id := by subst_solve_id

instance : SubstMapStable Ty Ty where
  apply_stable := by
    intro r σ h; funext; case _ t =>
    induction t generalizing r σ
      <;> simp [-Subst.rewrite_lift, -Subst.rewrite_lift_ren, -Subst.rewrite_lift_k_ren, *]
    case var => rw [<-h]; simp

instance : SubstMapRenComposeLeft Ty Ty where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Ty Ty where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Ty Ty where
  apply_compose := by subst_solve_compose

@[simp]
def SpineTy.rmap (r : Ren Ty) : SpineTy -> SpineTy
| ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ =>
  ⟨m1, Ks1, m2, Ks2, n, Vec.map (·⟨r.lift (m1 + m2)⟩) Ts, R⟨r.lift (m1 + m2)⟩⟩

instance : RenMap SpineTy Ty where
  rmap := SpineTy.rmap

@[simp]
theorem SpineTy.rmap_eq {r : Ren Ty}
  : (⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ : SpineTy)⟨r⟩
    = ⟨m1, Ks1, m2, Ks2, n, Ts⟨r.lift (m1 + m2)⟩, R⟨r.lift (m1 + m2)⟩⟩
:= by
  simp [RenMap.rmap]
  induction Ts <;> simp [Vec.rmap, *, RenMap.rmap]

@[simp]
def SpineTy.smap (σ : Subst Ty) : SpineTy -> SpineTy
| ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ =>
  ⟨m1, Ks1, m2, Ks2, n, Vec.map (·[σ.lift (m1 + m2)]) Ts, R[σ.lift (m1 + m2)]⟩

instance : SubstMap SpineTy Ty where
  smap := SpineTy.smap

@[simp]
theorem SpineTy.smap_eq {σ : Subst Ty}
  : (⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ : SpineTy)[σ]
    = ⟨m1, Ks1, m2, Ks2, n, Ts[σ.lift (m1 + m2)], R[σ.lift (m1 + m2)]⟩
:= by
  simp [SubstMap.smap]
  induction Ts <;> simp [Vec.smap, *, SubstMap.smap]

instance : SubstMapId SpineTy Ty where
  apply_id := by intro t; rcases t with ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩; simp

instance : SubstMapRenComposeLeft SpineTy Ty where
  apply_ren_compose_left := by
    intro t; rcases t with ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]

instance : SubstMapRenComposeRight SpineTy Ty where
  apply_ren_compose_right := by
    intro t; rcases t with ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]

instance : SubstMapCompose SpineTy Ty where
  apply_compose := by
    intro t; rcases t with ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]

theorem Ty.rmap_promote : Ty.rmap r A = A⟨r⟩ := by simp [RenMap.rmap]

theorem Ty.smap_promote : Ty.smap σ A = A[σ] := by simp [SubstMap.smap]

-- theorem Ty.rename_preserves_var_shape {r : Ren Ty} : t#x = T⟨r⟩ -> ∃ y,  (T = t#y ∧ x = r.act y) := by
--   sorry
--   -- intro h
--   -- induction T <;> simp at *
--   -- case var => simp [Ren.to] at h; assumption

-- theorem Ty.rename_preserves_global_shape {r : Ren} : gt#x = T[r] -> T = gt#x := by
--   intro h
--   induction T <;> simp at *
--   case var => simp [Ren.to] at h
--   case global => symm at h; assumption

-- theorem Ty.rename_preserves_arrow_shape {A B : Ty}{r : Ren} : A -:> B = T[r] ->
--   (∃ A' B' : Ty, (T = A' -:> B') ∧  A = A'[r] ∧ B = B'[r])
-- := by
--   intro h
--   induction T <;> simp at *
--   case var => simp [Ren.to] at h
--   case arrow a1 a2 _ _ => exists a1; exists a2

-- theorem Ty.rename_preserves_eq_shape {A B : Ty}{r : Ren} : (A ~[K]~ B) = T[r] ->
--   (∃ A' B' : Ty, (T = A' ~[K]~ B') ∧  A = A'[r] ∧ B = B'[r])
-- := by
--   intro h
--   induction T generalizing K  <;> simp at *
--   case var => simp [Ren.to] at h
--   case eq a1 a2 _ _  =>
--     cases h.1; cases h.2.1; cases h.2.2; clear h
--     exists a1; exists a2

-- theorem Ty.rename_preserves_app_shape {A B : Ty}{r : Ren} : (A • B) = T[r] ->
--   (∃ A' B' : Ty, (T = A' • B') ∧  A = A'[r] ∧ B = B'[r])
-- := by
--   intro h
--   induction T <;> simp at *
--   case var => simp [Ren.to] at h
--   case app a1 a2 _ _  =>
--     cases h.1; cases h.2; clear h
--     exists a1; exists a2


-- theorem Ty.rename_preserves_all_shape {P : Ty}{r : Ren} : (∀[K] P) = T[r] ->
--   (∃ P' : Ty, (T = ∀[K]P') ∧  P = P'[re 0::↑r ∘ +1:Ty])
-- := by
--   intro h
--   induction T generalizing K P <;> simp at *
--   case var => simp [Ren.to] at h
--   case all a ih =>
--     cases h.1; cases h.2; clear h
--     exists a;

end Core
