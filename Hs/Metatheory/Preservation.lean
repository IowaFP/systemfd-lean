import Hs.Compile


@[simp]
abbrev CompileCtxWfType : (v : CompileVariant) -> (Γ : Ctx HsTerm) -> (CompileJArgs v Γ) -> Prop
| .term => λ Γ => λ ⟨τ , k ; j, τ'⟩ => ∀ Γ',
  (k = `★) ->  CompileJ .term Γ ⟨τ, k ; j, τ'⟩ -> CompileJ .ctx Γ Γ' ->  Γ' ⊢ τ' : ★
  -- ∨ (k = `□ ->  Compile .term Γ (⟨τ, k ; j⟩, τ') ->  Compile .ctx Γ Γ' ->  Γ' ⊢ τ' : □)
| .ctx => λ Γ => λ Γ' => ⊢s Γ -> CompileJ .ctx Γ Γ' -> ⊢ Γ'

theorem compile_wf_ctx :
 CompileJ v Γ idx -> CompileCtxWfType v Γ idx := by sorry
-- by
-- intro j; induction j <;> simp at *;
-- case _ =>intros; apply Judgment.wfnil;
-- all_goals (intro j c; cases j; cases c)
-- case _ ih wf c =>
--   apply Judgment.wfempty (ih wf c)
-- case _ ih _ wf _ _ c1 c =>
--   apply Judgment.wfkind;
--   sorry;
--   apply (ih wf c);
-- case _ Γ' _ _ _ _ _ c ih1 ih2 wf h1 _ h2 c1 c2 =>
--   simp at Γ';
--   apply Judgment.wftype;
--   replace ih1 := ih1 wf c2;
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


theorem compile_type_preserving_index :
  CompileJ .ctx Γ Γ' ->
  (Γ d@ x).get_type = .some τ ->
  CompileJ .term Γ ⟨τ, k; j, τ'⟩ ->
  (Γ' d@ x).get_type = .some τ' := by
intro cc gt cτ;
induction x;
case _ => sorry
case _ => sorry

@[simp]
abbrev CompileTypePreservingType : (v : CompileVariant) -> (Γ : Ctx HsTerm) -> CompileJArgs v Γ -> Prop
| .term => λ Γ => λ ⟨t, τ ; j, t'⟩ => ∀ Γ' τ',
  ⊢s Γ ->
  CompileJ .ctx Γ Γ' ->
  ⊢ Γ' ->
  (jτ : Γ ⊢s τ : `★) ->
  CompileJ .term Γ ⟨τ, `★ ; jτ, τ'⟩ ->
  CompileJ .term Γ ⟨t, τ ; j, t'⟩ ->
  Γ' ⊢ t' : τ'
| .ctx => λ _ => λ _ => true

theorem compile_type_preserving :
  CompileJ v Γ idx ->
  CompileTypePreservingType v Γ idx
 := by sorry
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
