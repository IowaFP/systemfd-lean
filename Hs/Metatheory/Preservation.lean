import Hs.CompileJ


@[simp]
abbrev CompileCtxWfType : (v : CompileVariant) -> (Γ : Ctx HsTerm) -> (CompileJArgs v Γ) -> Prop
| .term => λ Γ => λ ⟨t , τ ; j , t'⟩ => ∀ Γ' τ',
  CompileJ .ctx Γ Γ' ->
  CompileJ .term Γ ⟨t, τ; j, t'⟩ ->
  (jk : Γ ⊢s τ : `★) ->
  CompileJ .type Γ ⟨τ, `★; jk, τ'⟩ ∧ (Γ' ⊢ t' : τ')
| .type => λ Γ => λ ⟨τ , k ; j , τ'⟩ => ∀ Γ',
  k = `★ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .type Γ ⟨τ, k; j, τ'⟩ ->
  (jk : Γ ⊢s k : `□) ->
  CompileJ .kind Γ ⟨k, `□; jk, ★⟩ ∧  (Γ' ⊢ τ' : ★)
| .kind => λ Γ => λ ⟨k , ki ; j , k'⟩ => ∀ Γ',
  ki = `□ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .kind Γ ⟨k, ki; j, k'⟩ ->
  (Γ' ⊢ k' : □)

| .ctx => λ Γ => λ Γ' => ⊢s Γ -> CompileJ .ctx Γ Γ' -> ⊢ Γ'

theorem compile_preserves_validctors :
  (j : Γ ⊢s τ : `★) ->
  ValidHsCtorType Γ τ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .type Γ ⟨τ, `★; j, τ'⟩ ->
  ValidCtorType Γ' τ' := by
intros j1 j2 j3 j4;
induction j2;
case _ v =>
  apply ValidCtorType.refl;
  unfold HsValidHeadVariable at v;
  unfold ValidHeadVariable; sorry
case _ => sorry
case _ => sorry
case _ => sorry



theorem compile_preserves_typing :
 CompileJ v Γ idx -> CompileCtxWfType v Γ idx :=
by
intro j; induction j <;> simp at *;
all_goals try (intro wf cc; cases cc; cases wf)
case _ => apply Judgment.wfnil
case _ ih cc wf =>
  apply Judgment.wfempty (ih wf cc);
case _  Γ' j c1 c2 ih1 ih2 _ _ j1 wf _ =>
  apply Judgment.wftype;
  have ih2' := ih2 Γ' c2 c1 (HsJudgment.ax wf);
  cases ih2'; assumption
  apply ih1 wf c2
case _ Γ' j1 c1 c2 ih1 ih2 j2 c3 c4 wf j4 =>
  apply Judgment.wfkind;
  apply ih2 Γ' c2 c1
  apply ih1 wf c2
case _ Γ' j1 c1 c2 ih1 ih2 j2 c3 c4 wf j4 =>
  apply Judgment.wfdatatype
  apply ih2 Γ' c2 c1
  apply ih1 wf c2
case _ Γ' j1 c1 c2 ih1 ih2 j2 c3 c4 wf j3 j4 =>
  apply Judgment.wfctor;
  have ih2' := ih2 Γ' c2 c1 (HsJudgment.ax wf);
  cases ih2'; assumption;
  apply ih1 wf c2
  apply compile_preserves_validctors j1 j4 c2 c1
case _ A' _ Γ' j1 j2 c1 c2 c3 ih1 ih2 ih3 j3 j4 c4 c5 c6 wf j5 j6 =>
  apply Judgment.wfterm;
  have ih3' := ih3 Γ' c3 c1 (HsJudgment.ax wf); cases ih3'; assumption
  have ih1' := ih1 Γ' A' c3 c2 j1;
  cases ih1'; assumption;
  apply ih2 wf c3

all_goals try (intro Γ' cc c1)
case _ wf =>
  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry


-- case _ => intros; apply Judgment.wfnil;
-- all_goals try (intro j c; cases j; cases c)
-- case _ ih wf c =>
--   apply Judgment.wfempty (ih wf c)
-- case _ Γ' _ c1 ih wf _ j1 c2 =>
--   apply Judgment.wftype;
--   apply (ih Γ' c1);
--   sorry
--   sorry
-- case _ Γ' j1 c1 ih1 wf _ j2 c2 =>
--   apply Judgment.wfkind;
--   replace ih1 := ih1 Γ' c1;
--   apply ih2 Γ' c; assumption;
--   apply ih1; assumption; assumption;
-- case _ Γ' _ _ _ _ _ _ h1' ih1 ih2 wf h1 h2 _ c1 c2 =>
--   simp at Γ'; apply Judgment.wfterm;
--   have ih2' := ih2 Γ' sorry h1' c2; assumption;
--   sorry
--   apply ih1 wf c2
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry


theorem compile_type_preserving_index :
  CompileJ .ctx Γ Γ' ->
  (Γ d@ x).get_type = .some τ ->
  CompileJ .term Γ ⟨τ, k; j, τ'⟩ ->
  (Γ' d@ x).get_type = .some τ' := by
intro cc gt cτ;
induction x;
case _ => sorry
case _ => sorry

-- @[simp]
-- abbrev CompileTypePreservingType : (v : CompileVariant) -> (Γ : Ctx HsTerm) -> CompileJArgs v Γ -> Prop
-- | .term => λ Γ => λ ⟨t, τ ; j, t'⟩ => ∀ Γ' τ',
--   ⊢s Γ ->
--   CompileJ .ctx Γ Γ' ->
--   ⊢ Γ' ->
--   (jτ : Γ ⊢s τ : `★) ->
--   CompileJ .term Γ ⟨τ, `★ ; jτ, τ'⟩ ->
--   CompileJ .term Γ ⟨t, τ ; j, t'⟩ ->
--   Γ' ⊢ t' : τ'
-- | .ctx => λ _ => λ _ => true

-- theorem compile_type_preserving :
--   CompileJ v Γ idx ->
--   CompileTypePreservingType v Γ idx
--  := by sorry
-- intro j; induction j <;> simp at *;
-- all_goals (intro Γ' τ' wf cc wf' jτ c1 c2)
-- case _ => sorry
-- case _ j1 j2 j3 ck1 ck2 ih1 ih2 => cases c1
-- case _ j1 c1 j2 j3 j4 c2 ih1 ih2 ih3 => -- bogus case
--   sorry
-- case _ =>
--   cases c2; case _ gt =>
--   have h := compile_type_preserving_index cc gt c1;
--   apply Judgment.var wf' (Eq.symm h)

-- theorem compile_valid_ctor_preserving :
--   (j : Γ ⊢s A : `★) ->
--   Compile A j A' ->
--   CompileCtx Γ Γ' ->
--   ValidHsCtorType Γ A ->
--   ValidCtorType Γ' A' := by
-- intro j c1 c2 h;
-- induction h;
-- case _ => sorry
-- case _ j' ih =>
--   have lem := compile_kind_preserving1 j
--   replace ih := ih j';
--   sorry
-- case _ => sorry
-- case _ => sorry
