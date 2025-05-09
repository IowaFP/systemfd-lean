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
def hs_weaken_frame :
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
  HsJudgment v Γ ix -> HsFrameWfByIndexLemmaType Γ v ix := by
intro v ix j
cases j <;> simp at *
case _ =>
  intro n; constructor; constructor
case _ Γ wf =>
  intro n;
  cases n <;> simp at *
  case _ => unfold Frame.apply; simp; constructor; constructor; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A j wf =>
  intro n;
  cases n <;> simp at *
  case _ =>
    have wf' := j.wftype wf
    have lem := hs_weaken_type wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_const] at lem; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A j wf =>
  intro n;
  cases n <;> simp at *
  case _ =>
    have wf' := j.wfkind wf
    have lem := hs_weaken_kind wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_HsKind] at lem; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A j wf =>
  intro n;
  cases n <;> simp at *
  case _ =>
    have wf' := j.wfdatatype wf
    have lem := hs_weaken_kind wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_HsKind] at lem; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A j wf =>
  intro n;
  cases n <;> simp at *
  case _ =>
    have wf' := j.wfopent wf
    have lem := hs_weaken_kind wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_HsKind] at lem; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A j wf vcty =>
  intro n;
  cases n <;> simp at *
  case _ =>
    have wf' := j.wfctor wf vcty
    have lem := hs_weaken_type wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_const] at lem; assumption
    apply hs_valid_ctor_weaken (.ctor A) wf' vcty
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
case _ Γ A t j1 j2 wf =>
  intro n
  cases n <;> simp at *
  case _ =>
    have wf' := j1.wfterm j2 wf
    have lem2 := hs_weaken_term wf' j2
    have lem1 := hs_weaken_type wf' j1
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_const] at lem1; assumption; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp

case _ Γ A j wf =>
  intro n
  cases n <;> simp at *
  case _ =>
    have wf' := j.wfopenm wf
    have lem := hs_weaken_type wf' j
    unfold Frame.apply; simp; constructor;
    rw[HsTerm.subst_const] at lem; assumption
  case _ n =>
    have lem := @hs_frame_wf_by_index_lemma Γ .ctx () wf; simp at lem;
    replace lem := lem n
    generalize zdef : Γ d@ n = f at *;
    apply HsFrameWf.weaken (λ x => x + 1) _ _ lem
    constructor; assumption; assumption
    case _ =>
      intro i; simp; unfold S; unfold Ren.to; simp
all_goals (apply 0)

def hs_frame_wf_by_index x : ⊢s Γ -> Γ ⊢s Γ d@ x :=
λ wf => hs_frame_wf_by_index_lemma .ctx () wf x

def hs_frame_wf_strength f : ⊢s (f :: Γ) -> ⊢s Γ :=
by
intro wwf
cases wwf
all_goals(assumption)

def hs_frame_wf f : ⊢s (f :: Γ) -> Γ ⊢s f :=
by
intro wwf
cases wwf
any_goals (constructor; assumption)
all_goals (assumption)


def hs_frame_wf_implies_wf : Γ ⊢s f -> ⊢s Γ
| .empty h1 => h1
| .kind h1 => hs_judgment_ctx_wf .kind h1
| .type h1 => hs_judgment_ctx_wf .type h1
| .datatype h1 => hs_judgment_ctx_wf .kind h1
| .ctor h1 _ => hs_judgment_ctx_wf .type h1
| .term h1 _ => hs_judgment_ctx_wf .type h1
| .openm h1 => hs_judgment_ctx_wf .type h1
| .opent h1 => hs_judgment_ctx_wf .kind h1

def hs_frame_wf_implies_wkn_wf : Γ ⊢s f -> ⊢s (f :: Γ) := by
intro h
cases f;
all_goals (cases h)
case empty => constructor; assumption;
case kind => constructor; assumption; apply hs_judgment_ctx_wf .kind; assumption
case datatype => constructor; assumption; apply hs_judgment_ctx_wf .kind; assumption
case opent => constructor; assumption; apply hs_judgment_ctx_wf .kind; assumption
case type => constructor; assumption; apply hs_judgment_ctx_wf .type; assumption
case ctor => constructor; assumption; apply hs_judgment_ctx_wf .type; assumption; assumption
case openm => constructor; assumption; apply hs_judgment_ctx_wf .type; assumption
case term => constructor; assumption; assumption; apply hs_judgment_ctx_wf .term; assumption
