import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch

theorem hs_rename_lift r (A : Frame HsTerm) :
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  ∀ x, ((A::Γ) d@ x).apply r.lift.to = (A.apply r.to::Δ) d@ (Ren.lift r x)
:= by
intro h x; simp
cases x <;> simp at *
case _ =>
  rw [Subst.lift_lemma]; simp
  unfold Ren.lift; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp
case _ x =>
  rw [Subst.lift_lemma]; simp
  unfold Ren.lift; simp
  rw [<-h x, Frame.apply_compose, Frame.apply_compose]; simp

@[simp]
abbrev hs_idx_ren (r : Ren) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .prf => λ (t, A) => ([r.to]t, [r.to]A)
  | .wf => λ () => ()

def hs_rename (r : Ren) : (v : JudgmentVariant) -> {idx : HsJudgmentArgs v} ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  HsJudgment v Δ (hs_idx_ren r idx)
| .prf, (t, τ) , j, wf, f => match j with
  | .implicitAllI h1 h2 h3 => sorry
  | .implicitAllE h1 h2 => sorry
  | .implicitArrI h1 h2 h3 h4 => sorry -- .implicitArrI (hs_rename r .prf h1 wf f) sorry sorry sorry
  | .implicitArrE h1 h2 => sorry
  | .ax wf' => .ax wf
  | .arrowk h1 h2 => .arrowk (hs_rename r .prf h1 wf f) (hs_rename r .prf h2 wf f)
  | .appk h1 h2 =>
    .appk (hs_rename r .prf h1 wf f) (hs_rename r .prf h2 wf f)
  | @HsJudgment.allt Γ A _ h1 h2 =>
      .allt (hs_rename r .prf h1 wf f) sorry
  | .arrow h1 h2  =>
    .arrow (hs_rename r .prf h1 wf f) sorry
           -- (by have h' := hs_rename r .prf h2 (.wfempty wf) (hs_rename_lift r .empty f); rw[Subst.lift_lemma]; sorry)
           -- (hs_rename r .prf h2 (by sorry) (by sorry))
  | .farrow h1 h3 h2  =>
    .farrow (hs_rename r .prf h1 wf f) sorry sorry
  | @HsJudgment.var Γ x T wf' h => .var wf (by
    have e := f x; unfold Frame.get_type at h;
    split at h;
    all_goals(cases h)
    case _ h =>
      have h' : (Γ d@ x).apply r.to = (Frame.kind T).apply r.to := by rw [h]
      rw [e] at h'; unfold Frame.apply at h'; simp at h';
      have h'' : (Δ d@ r x).get_type = (Frame.kind ([r.to] T)).get_type := by rw[h']
      symm at h'';apply h'';
    case _ h =>
      have h' : (Γ d@ x).apply r.to = (Frame.type T).apply r.to := by rw [h]
      rw [e] at h'; unfold Frame.apply at h'; simp at h';
      have h'' : (Δ d@ r x).get_type = (Frame.type ([r.to] T)).get_type := by rw[h']
      symm at h'';apply h'';
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry)
  | .lam h1 h2 h3 => .lam (hs_rename r .prf h1 wf f) sorry (hs_rename r .prf h3 wf f)
  | .app h1 h2 h3 =>
    .app (hs_rename r .prf h1 wf f) (hs_rename r .prf h2 wf f) (by rw [h3]; rw[<-Subst.lift_lemma]; sorry)
  | .hslet h1 h2 h3 h4 =>
    .hslet (hs_rename r .prf h1 wf f) (hs_rename r .prf h2 wf f) sorry (hs_rename r .prf h4 wf f)
  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    .hsIte (hs_rename r .prf h1 wf f) (hs_rename r .prf h2 wf f) (hs_rename r .prf h3 wf f) (hs_rename r .prf h4 wf f)
           (hs_rename r .prf h5 wf f) (hs_rename r .prf h6 wf f) sorry sorry (by sorry)  sorry
| .wf, () , j, wf, r => by simp; apply wf


def hs_weaken :
  ⊢s (f :: Γ) ->
  Γ ⊢s t : A ->
  (f::Γ) ⊢s ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .prf h wf (by intro; rw [Subst.to_S]; simp)

def hs_weaken_empty :
  Γ ⊢s t : A ->
  (.empty::Γ) ⊢s ([S]t) : ([S]A)
 := λ x => hs_weaken (.wfempty (hs_judgment_ctx_wf .prf x)) x

def hs_weaken_type :
  Γ ⊢s T : `★ ->
  Γ ⊢s t : A ->
  (.type T::Γ) ⊢s ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken (.wftype h1 (hs_judgment_ctx_wf .prf h1)) h2

def hs_weaken_kind :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.kind T::Γ) ⊢s ([S]t) : ([S]A)
:= sorry

-- theorem weaken_kind :
--   Γ ⊢s T : `□ ->
--   Γ ⊢s t : A ->
--   (.kind T::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_datatype :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.datatype T::Γ) ⊢s ([S]t) : ([S]A)
:= sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_ctor :
  Γ ⊢s T : `★ ->
  ValidHsCtorType Γ T ->
  Γ ⊢s t : A ->
  (.ctor T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_opent :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.opent T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_openm :
  Γ ⊢s T : `★ ->
  Γ ⊢s t : A ->
  (.openm T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_insttype :
  Γ ⊢s T : `★ ->
  ValidHsInstType Γ T ->
  Γ ⊢s t : A ->
  (.insttype T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

-- theorem weaken_inst :
--   .openm T = Γ d@ x ->
--   Γ ⊢s b : T ->
--   Γ ⊢s t : A ->
--   (.inst #x b::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply j2; apply hs_judgment_ctx_wf j2
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_term :
  Γ ⊢s T : `★ ->
  Γ ⊢s b : T ->
  Γ ⊢s t : A ->
  (.term T b::Γ) ⊢s ([S]t) : ([S]A)
:= λ h1 h2 h3 => hs_weaken (.wfterm h1 h2 (hs_judgment_ctx_wf .prf h1)) h3
