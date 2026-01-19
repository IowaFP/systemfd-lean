import LeanSubst
import Core.Ty.Definition

open LeanSubst

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
def Ty.rmap (lf : Endo Ren) (r : Ren) : Ty -> Ty
| t#x => t#(r x)
| gt#x => gt#x
| A -[b]> B => rmap lf r A -[b]> rmap lf r B
| ∀[K] P => ∀[K] rmap lf (lf r) P
| app f a => rmap lf r f • rmap lf r a
| A ~[K]~ B => rmap lf r A ~[K]~ rmap lf r B

instance : RenMap Ty where
  rmap := Ty.rmap

@[simp]
def Ty.smap (lf : Endo (Subst Ty)) (σ : Subst Ty) : Ty -> Ty
| t#x => σ x
| gt#x => gt#x
| A -[b]> B => smap lf σ A -[b]> smap lf σ B
| ∀[K] P => ∀[K] smap lf (lf σ) P
| app f a => smap lf σ f • smap lf σ a
| A ~[K]~ B => smap lf σ A ~[K]~ smap lf σ B

instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
theorem Ty.subst_var : (t#x)[σ:Ty] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_global : (gt#x)[σ:Ty] = gt#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_arr {A B : Ty} : (A -[b]> B)[σ:Ty] = A[σ:_] -[b]> B[σ:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_all : (∀[K] P)[σ:Ty] = ∀[K] P[σ.lift:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_app : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_eq : (A ~[K]~ B)[σ:Ty] = A[σ:_] ~[K]~ B[σ:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_compose {x} {σ τ : Subst Ty}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Ty.from_action]

theorem Ty.apply_id {t : Ty} : t[+0] = t := by subst_solve_id Ty, Ty, t

instance : SubstMapId Ty Ty where
  apply_id := Ty.apply_id

theorem Ty.apply_stable (r : Ren) (σ : Subst Ty)
  : r.to = σ -> Ren.apply (T := Ty) r = Subst.apply σ
:= by subst_solve_stable Ty, r, σ

instance : SubstMapStable Ty where
  apply_stable := Ty.apply_stable

theorem Ty.apply_compose {s : Ty} {σ τ : Subst Ty} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Ty, s, σ, τ

instance : SubstMapCompose Ty Ty where
  apply_compose := Ty.apply_compose
