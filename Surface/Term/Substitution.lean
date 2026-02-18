import LeanSubst
import Surface.Term.Definition
import Surface.Ty

open LeanSubst

@[coe]
def Surface.Term.from_action : Subst.Action Surface.Term -> Surface.Term
| .re y => `#y
| .su t => t

@[simp]
theorem Surface.Term.from_action_id {n} : from_action (+0 n) = `#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Surface.Term.from_action_succ {n} : from_action (+1 n) = `#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Surface.Term.from_acton_re {n} : from_action (re n) = `#n := by simp [from_action]

@[simp]
theorem Surface.Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance Surface.instCoe_ActionTermTerm : Coe (Subst.Action Surface.Term) Surface.Term where
  coe := Surface.Term.from_action

@[simp]
def Surface.Term.rmap (lf : Endo Ren) (r : Ren) : Surface.Term -> Surface.Term
| `#x => `#(r x)
| g`#x => g`#x
| lamt A t => lamt A (rmap lf r t)
| lam A t => lam A (rmap lf (lf r) t)
| app t1 t2 => app (rmap lf r t1) (rmap lf r t2)
| appt t1 t2 => appt (rmap lf r t1) t2
| .match t1 t2 t3 t4 => .match (rmap lf r t1) (λ i => rmap lf r (t2 i)) (λ i => rmap lf r (t3 i)) (rmap lf r t4)

instance Surface.instRenMap_Term : RenMap Surface.Term where
  rmap := Surface.Term.rmap

@[simp]
def Surface.Term.Ty.smap (lf : Endo (Subst Surface.Ty)) (σ : Subst Surface.Ty) : Surface.Term -> Surface.Term
| `#x => `#x
| g`#x => g`#x
| app t1 t2 => app (smap lf σ t1) (smap lf σ t2)
| appt t1 t2 => appt (smap lf σ t1) t2[σ:_]
| lamt A t => lamt A (smap lf (lf σ) t)
| lam A t => lam A[σ:_] (smap lf σ t)
| .match t1 t2 t3 t4  => .match (smap lf σ t1) (λ i => smap lf σ (t2 i)) (λ i => smap lf σ (t3 i)) (smap lf σ t4)

instance Surface.instSubstMap_TermTy : SubstMap Surface.Term Surface.Ty where
  smap := Surface.Term.Ty.smap

@[simp]
def Surface.Term.smap (lf : Endo (Subst Term)) (σ : Subst Term) : Term -> Term
| `#x => σ x
| g`#x => g`#x
| app t1 t2 => app (smap lf σ t1) (smap lf σ t2)
| appt t1 t2 => appt (smap lf σ t1) t2
| lamt A t => lamt A (smap lf (σ ◾ +1@Surface.Ty) t)
| lam A t => lam A (smap lf (lf σ) t)
| .match t1 t2 t3 t4 => .match (smap lf σ t1) (λ i => smap lf σ (t2 i)) (λ i => smap lf σ (t3 i)) (smap lf σ t4)

instance Surface.instSubstMap_TermTerm : SubstMap Surface.Term Surface.Term where
  smap := Surface.Term.smap

@[simp]
theorem Surface.Term.subst_var : (`#x)[σ:Term] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Surface.Term.subst_global : (g`#x)[σ:Term] = g`#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Surface.Term.subst_app : (app t1 t2)[σ:Term] = app t1[σ:_] t2[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.subst_appt : (appt t1 t2)[σ:Term] = appt t1[σ:_] t2 := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.subst_lamt : (lamt A t)[σ:Term] = lamt A t[σ ◾ +1@Surface.Ty:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.subst_lam : (lam A t)[σ:Term] = lam A t[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.subst_match
  : (matchˢ! t1 t2 t3 t4)[σ:Term] = matchˢ! t1[σ:_] (λ i => (t2 i)[σ:_]) (λ i => (t3 i)[σ:_]) (t4[σ:_])
:= by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Surface.Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Surface.Term.from_action]

@[simp]
theorem Surface.Term.Ty.subst_var : (`#x)[σ:Surface.Ty] = `#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Surface.Term.Ty.subst_global : (g`#x)[σ:Surface.Ty] = g`#x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Surface.Term.Ty.subst_app : (app t1 t2)[σ:Surface.Ty] = app t1[σ:_] t2[σ:_] := by
  simp [Subst.apply, SubstMap.smap]
@[simp]
theorem Surface.Term.Ty.subst_appt : (appt t1 t2)[σ:Surface.Ty] = appt t1[σ:_] t2[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.Ty.subst_lamt : (lamt A t)[σ:Ty] = lamt A t[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.Ty.subst_lam : (lam A t)[σ:Ty] = lam A[σ:_] t[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Surface.Term.Ty.subst_match
  : (matchˢ! t1 ps t2 t3)[σ:Ty] = matchˢ! t1[σ:_] (λ i => (ps i)[σ:_]) (λ i => (t2 i)[σ:_]) t3[σ:_]
:= by
  simp [Subst.apply, SubstMap.smap]

theorem Surface.Term.Ty.apply_id {t : Surface.Term} : t[+0:Surface.Ty] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

instance Surface.instSubstMapId_Ty_TermTy : SubstMapId Surface.Term Surface.Ty where
  apply_id := Surface.Term.Ty.apply_id

@[simp]
theorem Surface.Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ) x = (Surface.Term.from_action (σ x))[τ:Ty]
:= by
  simp [Subst.hcompose, Surface.Term.from_action]
  generalize zdef : σ x = z
  cases z <;> simp

theorem Surface.Term.apply_stable (r : Ren) (σ : Subst Term)
  : r.to = σ -> Ren.apply (T := Term) r = Subst.apply σ
:= by subst_solve_stable Term, r, σ


instance Surface.instSubstMapStable_Term : SubstMapStable Surface.Term where
  apply_stable := Surface.Term.apply_stable

theorem Surface.Term.apply_ren_commute {s : Surface.Term} (r : Ren) (τ : Subst Surface.Ty)
  : s[r.to][τ:Surface.Ty] = s[τ:Surface.Ty][r.to]
:= by
  induction s generalizing r τ <;> simp [Ren.to] at *
  all_goals try simp [*]
  case lam A t ih =>
    replace ih := ih r.lift
    rw [Ren.to_lift (S := Surface.Term)] at ih; simp at ih
    apply ih

instance Surface.instSubstMapRenCommute_Term : SubstMapRenCommute Surface.Term Surface.Ty where
  apply_ren_commute := Surface.Term.apply_ren_commute

theorem Surface.Term.Ty.apply_compose {s : Term} {σ τ : Subst Ty} : s[σ:Ty][τ:_] = s[σ ∘ τ:_] := by
  subst_solve_compose Surface.Ty, s, σ, τ

instance Surface.instSubstMapCompose_TermTy : SubstMapCompose Surface.Term Surface.Ty where
  apply_compose := Surface.Term.Ty.apply_compose

theorem Surface.Term.apply_hcompose {s : Surface.Term} {σ : Subst Surface.Term} {τ : Subst Surface.Ty}
  : s[σ][τ:_] = s[τ:_][σ ◾ τ]
:= by subst_solve_hcompose Surface.Term, Surface.Ty, s, σ, τ

instance Surface.instSubstMapHetCompose_TermTy : SubstMapHetCompose Surface.Term Surface.Ty where
  apply_hcompose := Surface.Term.apply_hcompose

theorem Surface.Term.apply_id {t : Term} : t[+0] = t := by subst_solve_id Term, Ty, t

instance Surface.instSubstMapId_TermTy : SubstMapId Surface.Term Surface.Term where
  apply_id := Surface.Term.apply_id

theorem Surface.Term.apply_compose {s : Surface.Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Term, s, σ, τ

instance Surface.instSubstMapCompose_TermTerm : SubstMapCompose Surface.Term Surface.Term where
  apply_compose := Surface.Term.apply_compose

inductive Surface.IteratedSubst where
| nil : IteratedSubst
| term : Subst Term -> IteratedSubst -> IteratedSubst
| type : Subst Ty -> IteratedSubst -> IteratedSubst

def Surface.Term.isubst (t : Surface.Term) : IteratedSubst -> Term
| .nil => t
| .term σ tl => t[σ].isubst tl
| .type σ tl => t[σ:Ty].isubst tl
