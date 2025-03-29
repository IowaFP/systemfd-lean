import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.Weaken
import Hs.Metatheory.TypeMatch

namespace FrameWf
  def weaken (r : Ren) :
    ⊢s Δ ->
    (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
    Γ ⊢s f ->
    Δ ⊢s f.apply r.to
  := by
  intro wf h j
  cases j
  case _ =>
    unfold Frame.apply; simp; constructor
    apply wf
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := rename r .prf j wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := rename r .prf j wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := rename r .prf j wf h; simp at lem
    apply lem
  case _ j1 j2 =>
    unfold Frame.apply; simp; constructor
    have lem := rename r .prf j1 wf h; simp at lem
    apply lem; apply valid_ctor_subst _ _ j2
    case _ =>
      intro n y h2; rw [h]
      unfold Ren.to at h2; simp at h2; subst h2
      simp
    case _ =>
      intro n h2; unfold Ren.to; simp
  -- case _ j =>
  --   unfold Frame.apply; simp; constructor
  --   have lem := rename r .prf j wf h; simp at lem
  --   apply lem
  -- case _ j =>
  --   unfold Frame.apply; simp; constructor
  --   have lem := rename r j wf h; simp at lem
  --   apply lem
  -- case _ j1 j2 =>
  --   unfold Frame.apply; simp; constructor
  --   have lem := rename r j1 wf h; simp at lem
  --   apply lem; apply valid_insttype_subst _ _ j2
  --   case _ =>
  --     intro n y h2; rw [h]
  --     unfold Ren.to at h2; simp at h2; subst h2
  --     simp
  --   case _ =>
  --     intro n h2; unfold Ren.to; simp
  -- case _ x T t j1 j2 =>
  --   have h2 := h x; rw [<-j1] at h2
  --   unfold Frame.apply at h2; simp at h2
  --   constructor; apply h2
  --   have lem := rename r j2 wf h; simp at lem
  --   apply lem
  case _ j1 j2 =>
    unfold Frame.apply; simp; constructor
    have lem1 := rename r .prf j1 wf h; simp at lem1; apply lem1
    have lem2 := rename r .prf j2 wf h; simp at lem2; apply lem2
end FrameWf

-- @[simp]
-- abbrev FrameWfByIndexLemmaType (Γ : Ctx HsTerm) : (v : JudgmentVariant) -> HsJudgmentArgs v -> Type
-- | .prf => λ _ => Int
-- | .wf => λ () => ∀ x, Γ ⊢s Γ d@ x

def hs_frame_wf_by_index_lemma : (v : JudgmentVariant) -> (ix : HsJudgmentArgs v)
  -> HsJudgment v Γ ix
  -> ∀ x, Γ ⊢s Γ d@ x
:= sorry


-- by
-- intro j; induction j <;> simp at *
-- case _ => constructor; constructor
-- case _ wf ih =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     unfold Frame.apply; simp; constructor
--     constructor; apply wf
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih x)
--     constructor; apply wf
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp
-- case _ j1 j2 ih1 ih2 =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     unfold Frame.apply; simp; constructor
--     have lem := weaken_type j1 j1; simp at lem
--     apply lem;
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
--     case _ => apply HsJudgment.wftype j1 j2
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp
-- case _ j1 j2 ih1 ih2 =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     unfold Frame.apply; simp; constructor
--     have lem := weaken_kind j1 j1; simp at lem
--     apply lem;
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
--     case _ => apply HsJudgment.wfkind j1 j2
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp
-- case _ j1 j2 ih1 ih2 =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     unfold Frame.apply; simp; constructor
--     have lem := weaken_datatype j1 j1; simp at lem
--     apply lem;
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
--     case _ => apply HsJudgment.wfdatatype j1 j2
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp
-- case _ j1 j2 j3 ih1 ih2 =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     unfold Frame.apply; simp; constructor
--     have lem := weaken_ctor j1 j3 j1; simp at lem
--     apply lem; apply valid_ctor_subst _ _ j3
--     case _ =>
--       intro n y h; unfold S at h
--       injection h with e; subst e; simp
--     case _ =>
--       intro n h; exists n + 1
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
--     case _ => apply HsJudgment.wfctor j1 j2 j3
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp
-- -- case _ j1 j2 ih1 ih2 =>
-- --   intro x; cases x <;> simp at *
-- --   case _ =>
-- --     unfold Frame.apply; simp; constructor
-- --     have lem := weaken_opent j1 j1; simp at lem
-- --     apply lem;
-- --   case _ x =>
-- --     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
-- --     case _ => apply HsJudgment.wfopent j1 j2
-- --     case _ =>
-- --       intro y; simp; unfold S; unfold Ren.to
-- --       simp
-- -- case _ j1 j2 ih1 ih2 =>
-- --   intro x; cases x <;> simp at *
-- --   case _ =>
-- --     unfold Frame.apply; simp; constructor
-- --     have lem := weaken_openm j1 j1; simp at lem
-- --     apply lem;
-- --   case _ x =>
-- --     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
-- --     case _ => apply Judgment.wfopenm j1 j2
-- --     case _ =>
-- --       intro y; simp; unfold S; unfold Ren.to
-- --       simp
-- -- case _ j1 j2 j3 ih1 ih2 =>
-- --   intro x; cases x <;> simp at *
-- --   case _ =>
-- --     unfold Frame.apply; simp; constructor
-- --     have lem := weaken_insttype j1 j3 j1; simp at lem
-- --     apply lem; apply valid_insttype_subst _ _ j3
-- --     case _ =>
-- --       intro n y h; unfold S at h
-- --       injection h with e; subst e; simp
-- --     case _ =>
-- --       intro n h; exists n + 1
-- --   case _ x =>
-- --     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
-- --     case _ => apply Judgment.wfinsttype j1 j2 j3
-- --     case _ =>
-- --       intro y; simp; unfold S; unfold Ren.to
-- --       simp
-- -- case _ Γ x T t j1 j2 j3 ih1 ih2 =>
-- --   have lem1 : .openm ([S]T) = (Γ d@ x).apply S := by
-- --     rw [<-j1]; unfold Frame.apply; simp
-- --   intro x; cases x <;> simp at *
-- --   case _ =>
-- --     have lem2 := weaken_inst j1 j2 j2; simp at lem2
-- --     unfold Frame.apply; simp; constructor
-- --     simp; apply lem1; apply lem2
-- --   case _ x =>
-- --     apply FrameWf.weaken (· + 1) _ _ (ih2 x)
-- --     case _ => apply Judgment.wfinst j1 j2 j3
-- --     case _ =>
-- --       intro y; simp; unfold S; unfold Ren.to
-- --       simp
-- case _ j1 j2 j3 ih1 ih2 ih3 =>
--   intro x; cases x <;> simp at *
--   case _ =>
--     have lem1 := weaken_term j1 j2 j1; simp at lem1
--     have lem2 := weaken_term j1 j2 j2; simp at lem2
--     unfold Frame.apply; simp; constructor
--     apply lem1; apply lem2
--   case _ x =>
--     apply FrameWf.weaken (· + 1) _ _ (ih3 x)
--     case _ => apply HsJudgment.wfterm j1 j2 j3
--     case _ =>
--       intro y; simp; unfold S; unfold Ren.to
--       simp

def hs_frame_wf_by_index x : ⊢s Γ -> Γ ⊢s Γ d@ x :=
λ wf => hs_frame_wf_by_index_lemma .wf () wf x

def hs_frame_wf_implies_wf : Γ ⊢s f -> ⊢s Γ
| .empty h1 => h1
| .kind h1 => hs_judgment_ctx_wf .prf h1
| .type h1 => hs_judgment_ctx_wf .prf h1
| .datatype h1 => hs_judgment_ctx_wf .prf h1
| .ctor h1 _ => hs_judgment_ctx_wf .prf h1
| .term h1 _ => hs_judgment_ctx_wf .prf h1


def hs_frame_wf_implies_typed_var T :
  Γ ⊢s Γ d@ x ->
  .some T = (Γ d@ x).get_type ->
  Γ ⊢s (.HsVar x) : T :=
λ fwf gt => HsJudgment.var (hs_frame_wf_implies_wf fwf) gt
