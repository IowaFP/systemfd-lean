import LeanSubst
import Core.Ty.Definition

open LeanSubst

def Subst.add (k : Nat) : Subst T := λ n => re (n + k)
namespace Core

@[coe]
def Ty.from_action : Subst.Action Ty -> Ty
| .re y => t#y
| .su t => t

@[simp]
theorem Ty.from_action_id {n} : from_action (+0 n) = t#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Ty.from_action_succ {n} : from_action (+1 n) = t#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Ty.from_acton_re {n} : from_action (re n) = t#n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (r : Ren) : Ty -> Ty
| t#x => t#(r x)
| gt#x => gt#x
| A -:> B => rmap r A -:> rmap r B
| ∀[K] P => ∀[K] rmap (r.lift) P
| app f a => rmap r f • rmap r a
| A ~[K]~ B => rmap r A ~[K]~ rmap r B

instance : RenMap Ty where
  rmap := Ty.rmap

@[simp]
def Ty.smap (σ : Subst Ty) : Ty -> Ty
| t#x => σ x
| gt#x => gt#x
| A -:> B => smap σ A -:> smap σ B
| ∀[K] P => ∀[K] smap σ.lift P
| app f a => smap σ f • smap σ a
| A ~[K]~ B => smap σ A ~[K]~ smap σ B

instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
theorem Ty.subst_var : (t#x)[σ:Ty] = σ x := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_global : (gt#x)[σ:Ty] = gt#x := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_arr {A B : Ty} : (A -:> B)[σ:Ty] = A[σ:_] -:> B[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_all : (∀[K] P)[σ:Ty] = ∀[K] P[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_app : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.subst_eq : (A ~[K]~ B)[σ:Ty] = A[σ:_] ~[K]~ B[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_compose {x} {σ τ : Subst Ty}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Ty.from_action]

theorem Ty.apply_id {t : Ty} : t[+0] = t := by
  induction t; all_goals(simp at *; try simp [*])

instance : SubstMapId Ty Ty where
  apply_id := Ty.apply_id

theorem Ty.apply_stable (r : Ren) (σ : Subst Ty)
  : r = σ -> rmap r = smap σ
:= by subst_solve_stable  r, σ

instance : SubstMapStable Ty where
  apply_stable := Ty.apply_stable

theorem Ty.apply_compose {s : Ty} {σ τ : Subst Ty} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Ty, s, σ, τ

instance : SubstMapCompose Ty Ty where
  apply_compose := Ty.apply_compose

theorem Ty.rename_preserves_var_shape {r : Ren} : t#x = T[r] -> ∃ y,  (T = t#y ∧ x = r y) := by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h; assumption


theorem Ty.rename_preserves_global_shape {r : Ren} : gt#x = T[r] -> T = gt#x := by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case global => symm at h; assumption


theorem Ty.rename_preserves_arrow_shape {A B : Ty}{r : Ren} : A -:> B = T[r] ->
  (∃ A' B' : Ty, (T = A' -:> B') ∧  A = A'[r] ∧ B = B'[r])
:= by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case arrow a1 a2 _ _ => exists a1; exists a2

theorem Ty.rename_preserves_eq_shape {A B : Ty}{r : Ren} : (A ~[K]~ B) = T[r] ->
  (∃ A' B' : Ty, (T = A' ~[K]~ B') ∧  A = A'[r] ∧ B = B'[r])
:= by
intro h
induction T generalizing K  <;> simp at *
case var => simp [Ren.to] at h
case eq a1 a2 _ _  =>
  cases h.1; cases h.2.1; cases h.2.2; clear h
  exists a1; exists a2

theorem Ty.rename_preserves_app_shape {A B : Ty}{r : Ren} : (A • B) = T[r] ->
  (∃ A' B' : Ty, (T = A' • B') ∧  A = A'[r] ∧ B = B'[r])
:= by
intro h
induction T <;> simp at *
case var => simp [Ren.to] at h
case app a1 a2 _ _  =>
  cases h.1; cases h.2; clear h
  exists a1; exists a2


theorem Ty.rename_preserves_all_shape {P : Ty}{r : Ren} : (∀[K] P) = T[r] ->
  (∃ P' : Ty, (T = ∀[K]P') ∧  P = P'[re 0::↑r ∘ +1:Ty])
:= by
intro h
induction T generalizing K P <;> simp at *
case var => simp [Ren.to] at h
case all a ih =>
  cases h.1; cases h.2; clear h
  exists a;

end Core
