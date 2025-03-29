import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch

theorem rename_lift r (A : Frame HsTerm) :
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
abbrev idx_ren (r : Ren) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .prf => λ (t, A) => ([r.to]t, [r.to]A)
  | .wf => λ () => ()

def rename (r : Ren) : (v : JudgmentVariant) -> {idx : HsJudgmentArgs v} ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  HsJudgment v Δ (idx_ren r idx)
| .prf, (t, τ) , j, wf, f => match j with
  | .implicitAllI h1 h2 => .implicitAllI sorry (rename r .prf h2 wf f)
  | .implicitAllE h1 h2 => sorry
  | .implicitArrI h1 h2 h3 => .implicitArrI (rename r .prf h1 wf f) sorry (rename r .prf h3 wf f)
  | .implicitArrE h1 h2 => sorry
  | .ax wf' => .ax wf
  | .arrowk h1 h2 => .arrowk (rename r .prf h1 wf f) (rename r .prf h2 wf f)
  | .appk h1 h2 =>
    .appk (rename r .prf h1 wf f) (rename r .prf h2 wf f)
  | @HsJudgment.allt Γ A _ h1 h2 =>
      .allt (rename r .prf h1 wf f) sorry
  | .arrow h1 h2  =>
    .arrow (rename r .prf h1 wf f) sorry
           -- (by have h' := rename r .prf h2 (.wfempty wf) (rename_lift r .empty f); rw[Subst.lift_lemma]; sorry)
           -- (rename r .prf h2 (by sorry) (by sorry))

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
  | .lam h1 h2 h3 => .lam (rename r .prf h1 wf f) sorry (rename r .prf h3 wf f)
  | .app h1 h2 h3 =>
    .app (rename r .prf h1 wf f) (rename r .prf h2 wf f) (by rw [h3]; rw[<-Subst.lift_lemma]; sorry)
  | .hslet h1 h2 h3 h4 =>
    .hslet (rename r .prf h1 wf f) (rename r .prf h2 wf f) sorry (rename r .prf h4 wf f)
  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    .hsIte (rename r .prf h1 wf f) (rename r .prf h2 wf f) (rename r .prf h3 wf f) (rename r .prf h4 wf f)
           (rename r .prf h5 wf f) (rename r .prf h6 wf f) sorry sorry (by sorry)  sorry
| .wf, () , j, wf, r => by simp; apply wf


def weaken :
  ⊢s (f :: Γ) ->
  Γ ⊢s t : A ->
  (f::Γ) ⊢s ([S]t) : ([S]A)
| wf , h => rename (λ x => x + 1) .prf h wf (by intro; rw [Subst.to_S]; simp)

def weaken_empty :
  Γ ⊢s t : A ->
  (.empty::Γ) ⊢s ([S]t) : ([S]A)
 := λ x => weaken (.wfempty (hs_judgment_ctx_wf .prf x)) x

def weaken_type :
  Γ ⊢s T : `★ ->
  Γ ⊢s t : A ->
  (.type T::Γ) ⊢s ([S]t) : ([S]A)
:= λ h1 h2 => weaken (.wftype h1 (hs_judgment_ctx_wf .prf h1)) h2

def weaken_kind :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.kind T::Γ) ⊢s ([S]t) : ([S]A)
:= sorry

-- theorem weaken_kind :
--   Γ ⊢s T : `□ ->
--   Γ ⊢s t : A ->
--   (.kind T::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2; apply rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_datatype :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.datatype T::Γ) ⊢s ([S]t) : ([S]A)
:= sorry
-- := by
-- intro j1 j2; apply rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_ctor :
  Γ ⊢s T : `★ ->
  ValidHsCtorType Γ T ->
  Γ ⊢s t : A ->
  (.ctor T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_opent :
  Γ ⊢s T : `□ ->
  Γ ⊢s t : A ->
  (.opent T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2; apply rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_openm :
  Γ ⊢s T : `★ ->
  Γ ⊢s t : A ->
  (.openm T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- by
-- intro j1 j2; apply rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_insttype :
  Γ ⊢s T : `★ ->
  ValidHsInstType Γ T ->
  Γ ⊢s t : A ->
  (.insttype T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

-- theorem weaken_inst :
--   .openm T = Γ d@ x ->
--   Γ ⊢s b : T ->
--   Γ ⊢s t : A ->
--   (.inst #x b::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2 j3; apply rename _ j3
-- case _ => constructor; apply j1; apply j2; apply hs_judgment_ctx_wf j2
-- case _ => intro x; simp; rw [Subst.to_S]

def weaken_term :
  Γ ⊢s T : `★ ->
  Γ ⊢s b : T ->
  Γ ⊢s t : A ->
  (.term T b::Γ) ⊢s ([S]t) : ([S]A)
:= λ h1 h2 h3 => weaken (.wfterm h1 h2 (hs_judgment_ctx_wf .prf h1)) h3
