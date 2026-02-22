import LeanSubst
import Surface.Term.Definition
import Surface.Ty

open LeanSubst

namespace Surface

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => `#y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0 n) = `#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1 n) = `#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = `#n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance instCoe_ActionTermTerm : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren) : Term -> Term
| `#x => `#(r x)
| g`#x => g`#x
| lamt A t => lamt A (rmap r t)
| lam A t => lam A (rmap r.lift t)
| app t1 t2 => app (rmap r t1) (rmap r t2)
| appt t1 t2 => appt (rmap r t1) t2
| .match t1 t2 t3 t4 => .match (rmap r t1) (rmap r <$> t2) (rmap r <$> t3) (rmap r t4)

instance instRenMap_Term : RenMap Term where
  rmap := Term.rmap

@[simp]
def Term.Ty.smap (σ : Subst Ty) : Term -> Term
| `#x => `#x
| g`#x => g`#x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| appt t1 t2 => appt (smap σ t1) t2[σ:_]
| lamt A t => lamt A (smap σ.lift t)
| lam A t => lam A[σ:_] (smap σ t)
| .match t1 t2 t3 t4  => .match (smap σ t1) (λ i => smap σ (t2 i)) (λ i => smap σ (t3 i)) (smap σ t4)

instance instSubstMap_TermTy : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| `#x => σ x
| g`#x => g`#x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| appt t1 t2 => appt (smap σ t1) t2
| lamt A t => lamt A (smap (σ ◾ +1@Ty) t)
| lam A t => lam A (smap σ.lift t)
| .match t1 t2 t3 t4 => .match (smap σ t1) (λ i => smap σ (t2 i)) (λ i => smap σ (t3 i)) (smap σ t4)

instance instSubstMap_TermTerm : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var : (`#x)[σ:Term] = σ x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_global : (g`#x)[σ:Term] = g`#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_app : (app t1 t2)[σ:Term] = app t1[σ:_] t2[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_appt : (appt t1 t2)[σ:Term] = appt t1[σ:_] t2 := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_lamt : (lamt A t)[σ:Term] = lamt A t[σ ◾ +1@Ty:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam : (lam A t)[σ:Term] = lam A t[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_match
  : (matchˢ! t1 t2 t3 t4)[σ:Term] = matchˢ! t1[σ:_] (λ i => (t2 i)[σ:_]) (λ i => (t3 i)[σ:_]) (t4[σ:_])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.subst_var : (`#x)[σ:Ty] = `#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_global : (g`#x)[σ:Ty] = g`#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_app : (app t1 t2)[σ:Ty] = app t1[σ:_] t2[σ:_] := by
  simp [SubstMap.smap]
@[simp]
theorem Term.Ty.subst_appt : (appt t1 t2)[σ:Ty] = appt t1[σ:_] t2[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lamt : (lamt A t)[σ:Ty] = lamt A t[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam : (lam A t)[σ:Ty] = lam A[σ:_] t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_match
  : (matchˢ! t1 ps t2 t3)[σ:Ty] = matchˢ! t1[σ:_] (λ i => (ps i)[σ:_]) (λ i => (t2 i)[σ:_]) t3[σ:_]
:= by
  simp [SubstMap.smap]

theorem Term.Ty.apply_id {t : Term} : t[+0:Ty] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

instance instSubstMapId_Ty_TermTy : SubstMapId Term Ty where
  apply_id := Term.Ty.apply_id

@[simp]
theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ) x = (Term.from_action (σ x))[τ:Ty]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ x = z
  cases z <;> simp

theorem Term.apply_stable (r : Ren) (σ : Subst Term)
  : r = σ -> rmap r =  smap σ
:= by subst_solve_stable r, σ


instance instSubstMapStable_Term : SubstMapStable Term where
  apply_stable := Term.apply_stable

theorem Term.apply_ren_commute {s : Term} (r : Ren) (τ : Subst Ty)
  : s[r.to][τ:Ty] = s[τ:Ty][r.to]
:= by
  induction s generalizing r τ <;> simp [Ren.to] at *
  all_goals try simp [*]
  case lam A t ih =>
    replace ih := ih r.lift
    rw [Ren.to_lift] at ih; simp at ih
    apply ih



instance instSubstMapRenCommute_Term : SubstMapRenCommute Term Ty where
  apply_ren_commute := Term.apply_ren_commute

theorem Term.Ty.apply_compose {s : Term} {σ τ : Subst Ty} : s[σ:Ty][τ:_] = s[σ ∘ τ:_] := by
  subst_solve_compose Ty, s, σ, τ

instance instSubstMapCompose_TermTy : SubstMapCompose Term Ty where
  apply_compose := Term.Ty.apply_compose

theorem Term.apply_hcompose {s : Term} {σ : Subst Term} {τ : Subst Ty}
  : s[σ][τ:_] = s[τ:_][σ ◾ τ]
:= by subst_solve_hcompose Term, Ty, s, σ, τ

instance instSubstMapHetCompose_TermTy : SubstMapHetCompose Term Ty where
  apply_hcompose := Term.apply_hcompose

theorem Term.apply_id {t : Term} : t[+0] = t := by induction t; all_goals (simp at *; try simp [*])

instance instSubstMapId_TermTy : SubstMapId Term Term where
  apply_id := Term.apply_id

theorem Term.apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Term, s, σ, τ

instance instSubstMapCompose_TermTerm : SubstMapCompose Term Term where
  apply_compose := Term.apply_compose

inductive IteratedSubst where
| nil : IteratedSubst
| term : Subst Term -> IteratedSubst -> IteratedSubst
| type : Subst Ty -> IteratedSubst -> IteratedSubst

def Term.isubst (t : Term) : IteratedSubst -> Term
| .nil => t
| .term σ tl => t[σ].isubst tl
| .type σ tl => t[σ:Ty].isubst tl

end Surface
