import LeanSubst
import Surface.Term.Definition
import Surface.Ty

open LeanSubst

namespace Surface

@[coe]
def Term.from_action : Action Term -> Term
| .re y => `#y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0σ.act n) = `#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1σ.act n) = `#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = `#n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance instCoe_ActionTermTerm : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| `#x => `#(r.act x)
| g`#x => g`#x
| lamt A t => lamt A (rmap r t)
| lam A t => lam A (rmap r.lift t)
| app t1 t2 => app (rmap r t1) (rmap r t2)
| appt t1 t2 => appt (rmap r t1) t2
-- | .match n t0 t1 t2 t3 t4 => .match n t0 (rmap r t1) (rmap r <$> t2) (rmap r <$> t3) (rmap r t4)
| annot t1 A => annot (rmap r t1) A

instance instRenMap_Term : RenMap Term Term where
  rmap := Term.rmap

@[simp]
def Term.Ty.rmap (r : Ren Ty) : Term -> Term
| `#x => `#x
| g`#x => g`#x
| lamt A t => lamt A (rmap r.lift t)
| lam A t => lam A⟨r⟩ (rmap r t)
| app t1 t2 => app (rmap r t1) (rmap r t2)
| appt t1 t2 => appt (rmap r t1) t2⟨r⟩
-- | .match m t0 t1 t2 t3 t4 =>  .match m t0⟨r⟩ (rmap r t1) (rmap r <$> t2) (rmap r <$> t3) (rmap r t4)
| annot t1 A => annot (rmap r t1) A⟨r⟩

instance : RenMap Term Ty where
  rmap := Term.Ty.rmap

@[simp]
def Term.Ty.smap (σ : Subst Ty) : Term -> Term
| `#x => `#x
| g`#x => g`#x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| appt t1 t2 => appt (smap σ t1) t2[σ]
| lamt A t => lamt A (smap σ.lift t)
| lam A t => lam A[σ] (smap σ t)
-- | .match n t0 t1 t2 t3 t4  => .match n t0 (smap σ t1) (λ i => smap σ (t2 i)) (λ i => smap σ (t3 i)) (smap σ t4)
| annot t1 A => annot (smap σ t1) A[σ]

instance instSubstMap_TermTy : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
theorem Term.ren_var {r : Ren Term} : (`#x)⟨r⟩ = `#(r.act x) := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_global {r : Ren Term} : (g`#x)⟨r⟩ = g`#x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_lam {r : Ren Term} : (lam A t)⟨r⟩ = lam A t⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_lamt {r : Ren Term} : (lamt A t)⟨r⟩ = lamt A t⟨r⟩ := by
  simp [RenMap.rmap]

-- @[simp]
-- theorem Term.ren_match {r : Ren Term}
--   : (.match n t0 t1 t2 t3 t4)⟨r⟩
--     = .match n (λ i => (t1 i)⟨r⟩) t2 (λ i => (t3 i)⟨r.lift (t2 i).bind⟩)
-- := by
--   simp [RenMap.rmap]


@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| `#x => σ.act x
| g`#x => g`#x
| app t1 t2 => app (smap σ t1) (smap σ t2)
| appt t1 t2 => appt (smap σ t1) t2
| lamt A t => lamt A (smap (σ ◾ Ren.succ Ty) t)
| lam A t => lam A (smap σ.lift t)
-- | .match n t0 t1 t2 t3 t4 => .match n t0 (smap σ t1) (λ i => smap σ (t2 i)) (λ i => smap σ (t3 i)) (smap σ t4)
| annot t1 A => annot (smap σ t1) A



instance instSubstMap_TermTerm : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var {σ : Subst Term} : (`#x)[σ] = σ.act x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_global {σ : Subst Term} : (g`#x)[σ] = g`#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_app {σ : Subst Term} : (app t1 t2)[σ] = app t1[σ] t2[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_appt {σ : Subst Term} : (appt t1 t2)[σ] = appt t1[σ] t2 := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_annoτ {σ : Subst Term} : (annot t1 t2)[σ] = annot t1[σ] t2 := by
  simp [SubstMap.smap]


@[simp]
theorem Term.subst_lamt {σ : Subst Term} : (lamt A t)[σ] = lamt A t[σ ◾ Ren.succ Ty] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam {σ : Subst Term} : (lam A t)[σ] = lam A t[σ.lift] := by
  simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_match {σ : Subst Term}
--   : (matchˢ! n t0 t1 t2 t3 t4)[σ] = matchˢ! n t0 t1[σ] (λ i => (t2 i)[σ]) (λ i => (t3 i)[σ]) (t4[σ])
-- := by
--   simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x : Nat} {σ τ : Subst Term}
  : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ.act x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.ren_var {r : Ren Ty} : (`#x)⟨r⟩ = `#x := by simp [RenMap.rmap]


@[simp]
theorem Term.Ty.subst_var {σ : Subst Ty} : (`#x)[σ] = `#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_global {σ : Subst Ty} : (g`#x)[σ] = g`#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_app {σ : Subst Ty} : (app t1 t2)[σ] = app t1[σ] t2[σ] := by
  simp [SubstMap.smap]
@[simp]
theorem Term.Ty.subst_appt {σ : Subst Ty} : (appt t1 t2)[σ] = appt t1[σ] t2[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lamt {σ : Subst Ty} : (lamt A t)[σ] = lamt A t[σ.lift] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam {σ : Subst Ty} : (lam A t)[σ] = lam A[σ] t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_annoτ {σ : Subst Ty} : (annot t A)[σ] = annot t[σ] A[σ] := by
  simp [SubstMap.smap]


-- @[simp]
-- theorem Term.Ty.subst_match
--   : (matchˢ! n t0 t1 ps t2 t3)[σ:Ty] = matchˢ! n t0 t1[σ:_] (λ i => (ps i)[σ:_]) (λ i => (t2 i)[σ:_]) t3[σ:_]
-- := by
--   simp [SubstMap.smap]


instance instSubstMapId_Ty_TermTy : SubstMapId Term Ty where
  apply_id := by subst_solve_id

@[simp]
theorem Term.hcompose_var {x : Nat}{σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ).act x = (Term.from_action (σ.act x))[τ]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

theorem Term.apply_stable (r : Ren Term) (σ : Subst Term)
  : r.to = σ -> rmap r =  smap σ
:= by sorry


instance instSubstMapStable_Term : SubstMapStable Term Term where
  apply_stable := Term.apply_stable

-- theorem Term.apply_ren_commute {s : Term} (r : Ren Ty) (τ : Subst Ty)
--   : s[r.to][τ] = s[τ][r.to]
-- := by
--   induction s generalizing r τ <;> simp [Ren.to] at *
--   all_goals try simp [*]
--   case lam A t ih =>
--     replace ih := ih r.lift
--     rw [Ren.to_lift] at ih; simp at ih
--     apply ih

-- instance instSubstMapRenCommute_Term : SubstMapRenCommute Term Ty where
--   apply_ren_commute := Term.apply_ren_commute

-- theorem Term.Ty.apply_compose {s : Term} {σ τ : Subst Ty} : s[σ:Ty][τ:_] = s[σ ∘ τ:_] := by
--   subst_solve_compose Ty, s, σ, τ

-- instance instSubstMapCompose_TermTy : SubstMapCompose Term Ty where
--   apply_compose := Term.Ty.apply_compose

-- theorem Term.apply_hcompose {s : Term} {σ : Subst Term} {τ : Subst Ty}
--   : s[σ][τ:_] = s[τ:_][σ ◾ τ]
-- := by subst_solve_hcompose Term, Ty, s, σ, τ

-- instance instSubstMapHetCompose_TermTy : SubstMapHetCompose Term Ty where
--   apply_hcompose := Term.apply_hcompose

-- theorem Term.apply_id {t : Term} : t[+0] = t := by induction t; all_goals (simp at *; try simp [*])

-- instance instSubstMapId_TermTy : SubstMapId Term Term where
--   apply_id := Term.apply_id

-- theorem Term.apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
--   subst_solve_compose Term, s, σ, τ

-- instance instSubstMapCompose_TermTerm : SubstMapCompose Term Term where
--   apply_compose := Term.apply_compose

end Surface
