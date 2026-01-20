import LeanSubst
import Core.Term.Definition

open LeanSubst

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0 n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1 n) = #(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (lf : Endo Ren) (r : Ren) : Term -> Term
| #x => #(r x)
| g#x => g#x
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (rmap lf r t)
| ctor2 c t1 t2 => ctor2 c (rmap lf r t1) (rmap lf r t2)
| tbind v A t => tbind v A (rmap lf r t)
| lam b A t => lam b A (rmap lf (lf r) t)
| guard t1 t2 t3 => guard (rmap lf r t1) (rmap lf r t2) (rmap lf r t3)
| .match t1 ts => .match (rmap lf r t1) (λ i => rmap lf r (ts i))

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
def Ctor0Variant.rmap (_ : Endo Ren) (_ : Ren) : Ctor0Variant -> Ctor0Variant
| c => c

instance : RenMap Ctor0Variant where
  rmap := Ctor0Variant.rmap

@[simp]
def Ctor0Variant.smap (_ : Endo (Subst Ctor0Variant)) (_ : Subst Ctor0Variant) : Ctor0Variant -> Ctor0Variant
| c => c

instance : SubstMap Ctor0Variant Ctor0Variant where
  smap := Ctor0Variant.smap

@[simp]
theorem Ctor0Variant.subst_ {c : Ctor0Variant} : c[σ:Ctor0Variant] = c := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor0Variant Ctor0Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor0Variant Ctor0Variant where
  apply_compose := by simp

@[simp]
def Ctor0Variant.Ty.smap (_ : Endo (Subst Ty)) (σ : Subst Ty) : Ctor0Variant -> Ctor0Variant
| zero => zero
| refl A => refl A[σ:_]

instance : SubstMap Ctor0Variant Ty where
  smap := Ctor0Variant.Ty.smap

@[simp]
theorem Ctor0Variant.subst_zero : zero[σ:Ty] = zero := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Ctor0Variant.subst_refl : (refl A)[σ:Ty] = refl A[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor0Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor0Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor0Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor1Variant.rmap (_ : Endo Ren) (_ : Ren) : Ctor1Variant -> Ctor1Variant
| c => c

instance : RenMap Ctor1Variant where
  rmap := Ctor1Variant.rmap

@[simp]
def Ctor1Variant.smap (_ : Endo (Subst Ctor1Variant)) (_ : Subst Ctor1Variant) : Ctor1Variant -> Ctor1Variant
| c => c

instance : SubstMap Ctor1Variant Ctor1Variant where
  smap := Ctor1Variant.smap

@[simp]
theorem Ctor1Variant.subst_ {c : Ctor1Variant} : c[σ:Ctor1Variant] = c := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor1Variant Ctor1Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor1Variant Ctor1Variant where
  apply_compose := by simp

@[simp]
def Ctor1Variant.Ty.smap (_ : Endo (Subst Ty)) (σ : Subst Ty) : Ctor1Variant -> Ctor1Variant
| sym => sym
| fst => fst
| snd => snd
| appt a => appt a[σ:_]

instance : SubstMap Ctor1Variant Ty where
  smap := Ctor1Variant.Ty.smap

@[simp]
theorem Ctor1Variant.subst_sym : sym[σ:Ty] = sym := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Ctor1Variant.subst_fst : (fst)[σ:Ty] = fst := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Ctor1Variant.subst_snd : (snd)[σ:Ty] = snd := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Ctor1Variant.subst_appt : (appt a)[σ:Ty] = appt a[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor1Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor1Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor1Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor2Variant.rmap (_ : Endo Ren) (_ : Ren) : Ctor2Variant -> Ctor2Variant
| c => c

instance : RenMap Ctor2Variant where
  rmap := Ctor2Variant.rmap

@[simp]
def Ctor2Variant.smap (_ : Endo (Subst Ctor2Variant)) (_ : Subst Ctor2Variant) : Ctor2Variant -> Ctor2Variant
| c => c

instance : SubstMap Ctor2Variant Ctor2Variant where
  smap := Ctor2Variant.smap

@[simp]
theorem Ctor2Variant.subst_ {c : Ctor2Variant} : c[σ:Ctor2Variant] = c := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor2Variant Ctor2Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor2Variant Ctor2Variant where
  apply_compose := by simp

@[simp]
def Ctor2Variant.Ty.smap (_ : Endo (Subst Ty)) (_ : Subst Ty) : Ctor2Variant -> Ctor2Variant
| c => c

instance : SubstMap Ctor2Variant Ty where
  smap := Ctor2Variant.Ty.smap

@[simp]
theorem Ctor2Variant.Ty.subst_ {c : Ctor2Variant} : c[σ:Ty] = c := by
  simp [Subst.apply, SubstMap.smap]

instance : SubstMapId Ctor2Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor2Variant Ty where
  apply_compose := by simp

instance : SubstMapHetCompose Ctor2Variant Ty where
  apply_hcompose := by simp

@[simp]
def Term.Ty.smap (lf : Endo (Subst Ty)) (σ : Subst Ty) : Term -> Term
| #x => #x
| g#x => g#x
| ctor0 c => ctor0 c[σ:Ty]
| ctor1 c t => ctor1 c[σ:Ty] (smap lf σ t)
| ctor2 c t1 t2 => ctor2 c[σ:Ty] (smap lf σ t1) (smap lf σ t2)
| tbind v A t => tbind v A (smap lf (lf σ) t)
| lam b A t => lam b A[σ:_] (smap lf σ t)
| guard t1 t2 t3 => guard (smap lf σ t1) (smap lf σ t2) (smap lf σ t3)
| .match t1 ts => .match (smap lf σ t1) (λ i => smap lf σ (ts i))

instance : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (lf : Endo (Subst Term)) (σ : Subst Term) : Term -> Term
| #x => σ x
| g#x => g#x
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (smap lf σ t)
| ctor2 c t1 t2 => ctor2 c (smap lf σ t1) (smap lf σ t2)
| tbind v A t => tbind v A (smap lf (σ ◾ +1@Ty) t)
| lam b A t => lam b A (smap lf (lf σ) t)
| guard t1 t2 t3 => guard (smap lf σ t1) (smap lf σ t2) (smap lf σ t3)
| .match t1 ts => .match (smap lf σ t1) (λ i => smap lf σ (ts i))

instance : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var : (#x)[σ:Term] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_global : (g#x)[σ:Term] = g#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor0 : (ctor0 v)[σ:Term] = ctor0 v := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_ctor1 : (ctor1 v t)[σ:Term] = ctor1 v t[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_ctor2 : (ctor2 v t1 t2)[σ:Term] = ctor2 v t1[σ:_] t2[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_tbind : (tbind v A t)[σ:Term] = tbind v A t[σ ◾ +1@Ty:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_lam : (lam b A t)[σ:Term] = lam b A t[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_guard : (guard t1 t2 t3)[σ:Term] = guard t1[σ:_] t2[σ:_] t3[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.subst_match
  : (match! t1 t2)[σ:Term] = match! t1[σ:_] (λ i => (t2 i)[σ:_])
:= by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.subst_var : (#x)[σ:Ty] = #x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_global : (g#x)[σ:Ty] = g#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor0 : (ctor0 c)[σ:Ty] = ctor0 c[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor1 : (ctor1 c t)[σ:Ty] = ctor1 c[σ:_] t[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor2 : (ctor2 c t1 t2)[σ:Ty] = ctor2 c[σ:_] t1[σ:_] t2[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tbind : (tbind b A t)[σ:Ty] = tbind b A t[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam : (lam b A t)[σ:Ty] = lam b A[σ:_] t[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_guard : (guard t1 t2 t3)[σ:Ty] = guard t1[σ:_] t2[σ:_] t3[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_match
  : (match! t1 t2)[σ:Ty] = match! t1[σ:_] (λ i => (t2 i)[σ:_])
:= by
  simp [Subst.apply, SubstMap.smap]

theorem Term.Ty.apply_id {t : Term} : t[+0:Ty] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

instance : SubstMapId Term Ty where
  apply_id := Term.Ty.apply_id

@[simp]
theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ) x = (Term.from_action (σ x))[τ:Ty]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ x = z
  cases z <;> simp

theorem Term.apply_stable (r : Ren) (σ : Subst Term)
  : r.to = σ -> Ren.apply (T := Term) r = Subst.apply σ
:= by subst_solve_stable Term, r, σ

instance : SubstMapStable Term where
  apply_stable := Term.apply_stable

theorem Term.apply_ren_commute {s : Term} (r : Ren) (τ : Subst Ty)
  : s[r.to][τ:Ty] = s[τ:Ty][r.to]
:= by
  induction s generalizing r τ <;> simp [Ren.to] at *
  all_goals try simp [*]
  case lam A t ih =>
    replace ih := ih r.lift
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    apply ih

instance : SubstMapRenCommute Term Ty where
  apply_ren_commute := Term.apply_ren_commute

theorem Term.Ty.apply_compose {s : Term} {σ τ : Subst Ty} : s[σ:Ty][τ:_] = s[σ ∘ τ:_] := by
  subst_solve_compose Ty, s, σ, τ

instance : SubstMapCompose Term Ty where
  apply_compose := Term.Ty.apply_compose

theorem Term.apply_hcompose {s : Term} {σ : Subst Term} {τ : Subst Ty}
  : s[σ][τ:_] = s[τ:_][σ ◾ τ]
:= by subst_solve_hcompose Term, Ty, s, σ, τ

instance : SubstMapHetCompose Term Ty where
  apply_hcompose := Term.apply_hcompose

theorem Term.apply_id {t : Term} : t[+0] = t := by subst_solve_id Term, Ty, t

instance : SubstMapId Term Term where
  apply_id := Term.apply_id

theorem Term.apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Term, s, σ, τ

instance : SubstMapCompose Term Term where
  apply_compose := Term.apply_compose
