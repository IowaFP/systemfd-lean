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
  | .term => λ (t, A) => ([r.to]t, [r.to]A)
  | .kind => λ (t, A) => ([r.to]t, [r.to]A)
  | .type => λ (t, A) => ([r.to]t, [r.to]A)
  | .ctx => λ () => ()

def hs_rename (r : Ren) : (v : HsVariant) -> {idx : HsJudgmentArgs v} ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  HsJudgment v Δ (hs_idx_ren r idx)
| .kind, (t, τ) , j, wf, f => match j with
  | .ax wf' => .ax wf
  | .arrowk h1 h2 => .arrowk (hs_rename r .kind h1 wf f) (hs_rename r .kind h2 wf f)
| .type, (t, τ) , j, wf, f => match j with
  | @HsJudgment.varTy Γ x t wf test gt _ => sorry
  | .appk h1 h2 h3 h4 =>
    .appk (hs_rename r .type h1 wf f) (hs_rename r .type h2 wf f) (hs_rename r .kind h3 wf f) (hs_rename r .kind h4 wf f)
  | @HsJudgment.allt Γ A _ h1 h2 =>
      .allt (hs_rename r .kind h1 wf f) sorry
  | .arrow h1 h2 =>
    .arrow (hs_rename r .type h1 wf f) sorry
           -- (by have h' := hs_rename r .prf h2 (.wfempty wf) (hs_rename_lift r .empty f); rw[Subst.lift_lemma]; sorry)
           -- (hs_rename r .prf h2 (by sorry) (by sorry))
  | .farrow h1 h3 h2  =>
    .farrow (hs_rename r .type h1 wf f) sorry sorry
| .term, (t, τ) , j, wf, f => match j with
  | .implicitAllI h1 h2 h3 => sorry
  | .implicitAllE h1 h2 h3 h4 => sorry
  | .implicitArrI h1 h2 h3 h4 => sorry -- .implicitArrI (hs_rename r .prf h1 wf f) sorry sorry sorry
  | .implicitArrE h1 h2 => sorry
  | @HsJudgment.var Γ x T wf' h _ => .var sorry sorry sorry
  | .lam h1 h2 h3 => .lam (hs_rename r .type h1 wf f) sorry sorry
  | .app h1 h2 h3 =>
    .app (hs_rename r .term h1 wf f) (hs_rename r .term h2 wf f) (by rw [h3]; rw[<-Subst.lift_lemma]; sorry)
  | .hslet h1 h2 h3 h4 =>
    .hslet (hs_rename r .type h1 wf f) (hs_rename r .term h2 wf f) sorry (hs_rename r .type h4 wf f)
  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    .hsIte (hs_rename r .term h1 wf f) (hs_rename r .term h2 wf f) (hs_rename r .term h3 wf f) (hs_rename r .term h4 wf f)
           (hs_rename r .type h5 wf f) (hs_rename r .type h6 wf f) sorry sorry (by sorry)  sorry
| .ctx, () , j, wf, r => by simp; apply wf


def hs_weaken_type :
  ⊢s (f :: Γ) ->
  Γ ⊢τ t : A ->
  (f::Γ) ⊢τ ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .type h wf (by intro; rw [Subst.to_S]; simp)

def hs_weaken_kind :
  ⊢s (f :: Γ) ->
  Γ ⊢κ t : A ->
  (f::Γ) ⊢κ ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .kind h wf (by intro; rw [Subst.to_S]; simp)

def hs_weaken_kind_unique :
  ⊢s (f :: Γ) ->
  Γ ⊢κ t : A ->
  (f::Γ) ⊢κ t : A
| wf , HsJudgment.ax wf' => HsJudgment.ax wf
| wf , .arrowk h1 h2 => HsJudgment.arrowk (hs_weaken_kind_unique wf h1) (hs_weaken_kind_unique wf h2)


def hs_weaken_term :
  ⊢s (f :: Γ) ->
  Γ ⊢t t : A ->
  (f::Γ) ⊢t ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .term h wf (by intro; rw [Subst.to_S]; simp)


def hs_weaken_empty_term :
  Γ ⊢t t : A ->
  (.empty::Γ) ⊢t ([S]t) : ([S]A)
 := λ x => hs_weaken_term (.wfempty (hs_judgment_ctx_wf .term x)) x

def hs_weaken_empty_type :
  Γ ⊢τ t : A ->
  (.empty::Γ) ⊢τ ([S]t) : ([S]A)
 := λ x => hs_weaken_type (.wfempty (hs_judgment_ctx_wf .type x)) x

def hs_weaken_empty_kind :
  Γ ⊢κ t : A ->
  (.empty::Γ) ⊢κ ([S]t) : ([S]A)
 := λ x => hs_weaken_kind (.wfempty (hs_judgment_ctx_wf .kind x)) x


def hs_weaken_type_term :
  Γ ⊢τ T : `★ ->
  Γ ⊢t t : A ->
  (.type T::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken_term (.wftype h1 (hs_judgment_ctx_wf .type h1)) h2

def hs_weaken_kind_term :
  Γ ⊢κ T : `□ ->
  Γ ⊢t t : A ->
  (.kind T::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken_term (.wfkind h1 (hs_judgment_ctx_wf .kind h1)) h2

-- theorem weaken_kind :
--   Γ ⊢s T : `□ ->
--   Γ ⊢s t : A ->
--   (.kind T::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_datatype_term :
  Γ ⊢κ T : `□ ->
  Γ ⊢t t : A ->
  (.datatype T::Γ) ⊢t ([S]t) : ([S]A)
:= sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_ctor :
  Γ ⊢τ T : `★ ->
  ValidHsCtorType Γ T ->
  Γ ⊢t t : A ->
  (.ctor T::Γ) ⊢t ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_opent :
  Γ ⊢κ T : `□ ->
  Γ ⊢t t : A ->
  (.opent T::Γ) ⊢κ ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

-- def hs_weaken_openm :
--   Γ ⊢s T : `★ ->
--   Γ ⊢s t : A ->
--   (.openm T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

-- def hs_weaken_insttype :
--   Γ ⊢s T : `★ ->
--   ValidHsInstType Γ T ->
--   Γ ⊢s t : A ->
--   (.insttype T::Γ) ⊢s ([S]t) : ([S]A) := sorry
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

def hs_weaken_term_term :
  Γ ⊢τ T : `★ ->
  Γ ⊢t b : T ->
  Γ ⊢t t : A ->
  (.term T b::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 h3 => hs_weaken_term (.wfterm h1 h2 (hs_judgment_ctx_wf .type h1)) h3

def hs_weaken_term_type :
  Γ ⊢τ T : `★ ->
  Γ ⊢t b : T ->
  Γ ⊢τ t : A ->
  (.term T b::Γ) ⊢τ ([S]t) : ([S]A)
:= λ h1 h2 h3 => hs_weaken_type (.wfterm h1 h2 (hs_judgment_ctx_wf .type h1)) h3
