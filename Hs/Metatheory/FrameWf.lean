import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.Weaken
import Hs.Metatheory.TypeMatch

namespace HsFrameWf
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
    have lem := hs_rename r .type j wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .kind j wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .kind j wf h; simp at lem
    apply lem
  case _ j1 j2 =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .type j1 wf h; simp at lem
    apply lem; apply hs_valid_ctor_subst _ _ j2
    case _ =>
      intro n y h2; rw [h]
      unfold Ren.to at h2; simp at h2; subst h2
      simp
    case _ =>
      intro n h2; unfold Ren.to; simp
  case _ j1 j2 =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .type j1 wf h; simp at lem
    apply lem
    have lem := hs_rename r .term j2 wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .kind j wf h; simp at lem
    apply lem
  case _ j =>
    unfold Frame.apply; simp; constructor
    have lem := hs_rename r .type j wf h; simp at lem
    apply lem

end HsFrameWf

namespace Ctx
def weaken_frame :
  ⊢s Γ ->
  Γ ⊢s f ->
  ⊢s (f::Γ) := by
intro wf f
cases f;
all_goals(constructor; assumption)
all_goals(assumption)
end Ctx

@[simp]
abbrev HsFrameWfByIndexLemmaType (Γ : Ctx HsTerm) : (v : HsVariant) -> HsJudgmentArgs v -> Type
| .term => λ _ => Int
| .type => λ _ => Int
| .kind => λ _ => Int
| .ctx => λ () => ∀ x, Γ ⊢s Γ d@ x

def hs_frame_wf_by_index_lemma : (v : HsVariant) -> (ix : HsJudgmentArgs v) ->
  HsJudgment v Γ ix -> HsFrameWfByIndexLemmaType Γ v ix
| .ctx, (), j => by
  simp at *; intro x;
  sorry
| .kind, args, j => by (simp at *); sorry
| .type, args, j => by (simp at args); sorry
| .term, args, j => by (simp at args); sorry

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
λ wf => hs_frame_wf_by_index_lemma .ctx () wf x

def hs_frame_wf_implies_wf : Γ ⊢s f -> ⊢s Γ
| .empty h1 => h1
| .kind h1 => hs_judgment_ctx_wf .kind h1
| .type h1 => hs_judgment_ctx_wf .type h1
| .datatype h1 => hs_judgment_ctx_wf .kind h1
| .ctor h1 _ => hs_judgment_ctx_wf .type h1
| .term h1 _ => hs_judgment_ctx_wf .type h1
| .openm h1 => hs_judgment_ctx_wf .type h1
| .opent h1 => hs_judgment_ctx_wf .kind h1

def hs_frame_wf_implies_typed_var T :
  Γ ⊢s Γ d@ x ->
  (Γ d@ x).is_ctor || (Γ d@ x).is_term || (Γ d@ x).is_type ->
  .some T = (Γ d@ x).get_type ->
  Γ ⊢t (`#x) : T :=
λ fwf h gt => HsJudgment.var (hs_frame_wf_implies_wf fwf) h gt

def hs_frame_wf_implies_kinded_varTy T :
  Γ ⊢s Γ d@ x ->
  (Γ d@ x).is_datatype || (Γ d@ x).is_kind ->
  .some T = (Γ d@ x).get_type ->
  Γ ⊢τ (`#x) : T :=
λ fwf h gt => HsJudgment.varTy (hs_frame_wf_implies_wf fwf) h gt
  (by generalize fh : Γ d@ x = f at *;
      cases f;
      all_goals(unfold Frame.get_type at gt; simp at gt)
      all_goals(unfold Frame.is_datatype at h; simp at h; cases h)
      all_goals(cases gt)
      sorry
      sorry)
