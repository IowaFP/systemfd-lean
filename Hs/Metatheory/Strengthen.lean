import Hs.Metatheory.Weaken
import Hs.Metatheory.FrameWf
import Mathlib.Logic.Equiv.Basic


def hs_stn_typing_lemma (r : Ren) :
  ⊢s Γ ->
  is_hs_kind k ->
  is_hs_type Δ ([r.to]t) ->
  (∀ x,  Δ d@ r x = (Γ d@x).apply r.to) ->
  Δ ⊢τ ([r.to]t) : ([r.to]k) ->
  Γ ⊢τ t : k := by
intro wf h1 h2 h3 j
cases t <;> cases k
all_goals try (simp at h1)
all_goals try (simp at h2)
case _ =>
  simp at j; unfold Ren.to at j; simp at j;
  unfold Ren.to at h2; simp at h2;
  cases j; case _ n h4 h5 h6 h7 =>
  apply HsJudgment.varTy
  apply wf
  rw[h3] at h5; simp at h5; simp;
  rw[<-Frame.is_datatype_apply] at h5
  rw[<-Frame.is_kind_apply] at h5
  assumption
  rw[h3] at h7;  sorry
  apply HsJudgment.ax wf
case _ v _ _ =>
  cases v <;> simp at h1
  simp at j; cases j;
  apply HsJudgment.varTy wf;
  sorry
  sorry
  sorry
case _ v _ _ =>
  cases v <;> simp at h2
  sorry
case _ v1 _ _ v2 _ _ =>
  cases v1 <;> simp at h2
  sorry
case _ v k τ =>
  cases v <;> simp at h2
  case _ =>
    simp at j; cases j; case _ j1 j2 =>
    apply HsJudgment.allt;
    sorry
    apply @hs_stn_typing_lemma (Frame.kind k :: Γ) `★ (Frame.kind ([r.to]k) :: Δ) τ (Ren.lift r)
    apply HsJudgment.wfkind; sorry; apply wf
    simp
    sorry
    sorry
    simp; sorry
  sorry
  sorry
case _ v _ _ _ _ _ =>
  cases v <;> simp at h2
  sorry
  sorry
  sorry




def hs_stn_kinding :
  Γ ⊢s f ->
  is_hs_kind k ->
  (f::Γ) ⊢κ ([S]k) : (`□) ->
  Γ ⊢κ k : `□ := by
intro wf hk j
cases k <;> try simp at hk
case _ =>
  apply HsJudgment.ax
  apply hs_frame_wf_implies_wf wf
case _ v _ _ =>
  cases v <;> simp at hk
  cases j; case _ A B h1 h2 =>
  apply HsJudgment.arrowk
  apply hs_stn_kinding wf hk.1 h1
  apply hs_stn_kinding wf hk.2 h2


def hs_stn_typing :
  Γ ⊢s f ->
  is_hs_kind k ->
  is_hs_type Γ t ->
  (f::Γ) ⊢τ ([S]t) : ([S]k) ->
  Γ ⊢τ t : k := by
intro wf h1 h2 h3
apply @hs_stn_typing_lemma Γ k (f :: Γ) t (λ x => x + 1)
apply hs_frame_wf_implies_wf wf
assumption
case _ =>
  cases t
  all_goals try (simp at h2)
  sorry
  case _ v A B =>
    cases v <;> simp at h2; simp
    constructor
    cases h3; sorry
    sorry
  case _ v _ _ =>
    cases v <;> simp at h2;
    sorry
    sorry
    sorry

case _ =>
  intro n
  simp; unfold S; unfold Ren.to; simp;
apply h3


-- intro τ k wf hk ht j
-- cases t
-- all_goals (unfold is_hs_type at ht; simp at ht)
-- all_goals (simp at j)
-- all_goals try (cases j)
-- case _ n wf test sk gt =>
--   apply HsJudgment.varTy
--   apply hs_frame_wf_strength f wf
--   simp at test; rw[<-Frame.is_datatype_apply] at test; rw[<-Frame.is_kind_apply] at test; simp; assumption
--   simp at gt;
--   case _ =>
--     have lem : Option.map (fun x => [S] x) (.some k) = .some ([S]k):= by simp
--     rw[<-lem]  at gt;
--     have lem2 := apply_fun_equiv (Option.map (fun x => [P] x)) gt; simp at lem2;
--     rw[lem2]; unfold Function.comp; simp
--   apply hs_stn_kinding k
--   apply hs_frame_wf f wf
--   assumption
--   apply sk

-- case _ =>
--   simp at ht;
--   sorry
-- case _ v A B =>
--   cases v
--   all_goals(simp at ht; cases k)
--   all_goals(simp at j; cases j)
--   case _ =>
--     sorry
--   case _ =>
--     sorry
--   case _ =>
--     sorry
