import Hs.Algorithm

inductive CompileCtx : Ctx HsTerm -> Ctx Term -> Prop where
| nil : CompileCtx [] []
| empty :
  ⊢s Γ ->
  CompileCtx Γ Γ' ->
  CompileCtx (.empty :: Γ) (.empty :: Γ')
| kind :
  ⊢s Γ ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢κ A : `□) ->
  compile_kind Γ A `□ j1 = .some A' ->
  CompileCtx (.kind A :: Γ) (.kind A' :: Γ')
| type :
  ⊢s Γ ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.type A :: Γ) (.type A' :: Γ')
| term :
  ⊢s Γ ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★)  ->
  (j2 : Γ ⊢t t : τ) ->
  compile_type Γ A `★ j = .some A' ->
  compile_term Γ t τ j2 = .some t' ->
  CompileCtx (.term A t :: Γ) (.term A' t' :: Γ')

theorem compile_ctx_type :
  CompileCtx Γ Γ' ->
  (Γ d@ x).get_type = .some τ ->
  (j : Γ ⊢τ `#x : τ) ->
  compile_type Γ `#x τ j = .some τ' ->
  (Γ' @ x).get_type = .some τ' :=
by
intro cc gt j c;
unfold compile_type at c; cases j; cases c;
case _ wf test gt =>
 clear gt;
 induction cc;
 case _ => cases test
 case _ =>
   induction x generalizing Γ Γ';
   case _ => cases gt;
   case _ ih1 ih2 =>
   sorry
 case _ => sorry
 case _ => sorry
 case _ => sorry


theorem compile_preserves_term_indices :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢t `#x : T) ->
  compile_type Γ T k j = .some T' ->
  (Γ' d@ x).get_type = .some T' := by
sorry

theorem kinding_uniqueness :
  Γ ⊢κ τ : k ->
  Γ ⊢κ τ : k' ->
  k = k' :=
 by
intro j1 j2
induction τ generalizing Γ k k'
case _ => cases j1; cases j2; rfl
all_goals (cases j1)
case _ ih1 ih2 kl1 kl2 =>
  cases j2; rfl;

theorem compile_preserves_kinds :
  CompileCtx Γ Γ' ->
  (j : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j = .some t' ->
  Γ' ⊢ t' : .kind := by
 intro cc j c;
 induction Γ, t, τ, j using compile_kind.induct generalizing t'
 all_goals try (cases e)
 case _ =>
   unfold compile_kind at c; cases c;
   case _ wf => sorry
     -- apply Judgment.ax;
     -- apply compile_ctx_wf wf cc
 case _ j1 j2 ih1 ih2 =>
   unfold compile_kind at c; simp at c;
   rw[Option.bind_eq_some] at c;
   cases c; case _ w1 c1 =>
   cases c1; case _ c1 c2 =>
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ w2 c2 =>
   cases c2; case _ c2 c3 =>
   cases c3;
   have ih1' := @ih1 w1 cc c1;
   have ih2' := @ih2 w2 cc c2;
   apply Judgment.allk;
   apply ih1';
   apply ih2'


def typing_js_gives_kinding_js :
  Γ ⊢τ t : k ->
  Γ ⊢κ k : `□ := by
intro j; sorry


theorem typing_uniqueness :
  Γ ⊢τ t : k ->
  Γ ⊢τ t : k' ->
  k = k' := by
intro j1 j2;
induction t generalizing Γ k k';
all_goals (cases j1)
case _ =>
  cases j2
  case _ h2 _ _ h1 =>
  rw [<-h1] at h2; injection h2;
all_goals(cases j2)
case _ ih1 ih2 A j1 j2 A' j1' j2' =>
  have u := @ih2 Γ A A' j1 j1'; subst u;
  have u := @ih1 Γ (A `-k> k) (A `-k> k') j2 j2';
  simp at u; apply u;
case _ => rfl
case _ => rfl
case _ => rfl

theorem compile_preserves_types :
  CompileCtx Γ Γ' ->
  (j2 : Γ ⊢κ k : `□) ->
  compile_kind Γ k `□ j2 = .some k' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  Γ' ⊢ τ' : k' := by
intro cc j1 c1 j2 c2;
induction Γ, τ, k, j2 using compile_type.induct generalizing Γ' τ' k'
all_goals (unfold compile_type at c2; simp at c2)
case _ Γ x wf test gt =>
     cases c2; sorry
  -- cases c2;
  -- apply Judgment.var;
  -- apply compile_ctx_wf; assumption; assumption;
  -- have lem1 := HsJudgment.varTy wf test gt
  -- have lem := compile_preserves_type_indices cc lem1 c1; symm at lem;
  -- assumption
case _ h1 h2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  apply Judgment.appk;
  case _ => sorry;
  case _ => sorry;
  case _ => sorry
case _ h1 h2 ih1 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e; unfold compile_kind at c1; cases j1;
  simp at c1; cases c1;
  apply Judgment.allt;
  apply compile_preserves_kinds cc h1 c2;
  apply @ih1 (.kind w1 :: Γ') ★ w2 _ _ _ c3
  case _ => apply CompileCtx.kind; assumption; assumption; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfkind; assumption; assumption
  case _ => unfold compile_kind; rfl

case _ j1 _ j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have lem1 := compile_preserves_kinds cc j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc _ _;
  case _ => apply c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl

  apply @ih2 (.empty::Γ') ★ w2 _ _ _ c3
  case _ => apply CompileCtx.empty; assumption; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl

case _ j1 _ j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have lem1 := compile_preserves_kinds cc j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  case _ tl1 tl2 _ =>
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 (.empty::Γ') ★ w2 _ _ _ c3
  case _ => apply CompileCtx.empty; assumption; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl

theorem compile_preserves_typing :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  (j2 : Γ ⊢t t : τ) ->
  compile_term Γ t τ j2 = .some t' ->
  Γ' ⊢ t' : τ' := by
intro cc j1 c1 j2 c2;
induction Γ, t, τ, j2 using compile_term.induct generalizing Γ' t' τ' k
all_goals (unfold compile_term at c2; simp at c2)
case _ wf test gt => sorry
  -- cases c2;
  -- have lem1 := HsJudgment.var wf test gt
  -- have lem := compile_preserves_term_indices cc lem1 c1
  -- apply Judgment.var;
  -- apply compile_ctx_wf wf cc
  -- sorry
case _ j1' j2 j3 ih1 =>
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ A' c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ t' c3 =>
 cases c3; case _ c3 e =>
 cases e;
 have uniq := typing_uniqueness j1 j3; subst uniq;
 unfold compile_type at c1; cases j1; simp at c1;
 rw[Option.bind_eq_some] at c1;
 cases c1; case _ x1 c1' =>
 cases c1'; case _ c1' c2' =>
 rw[Option.bind_eq_some] at c2';
 cases c2'; case _ B' c2' =>
 cases c2'; case _ c2' e =>
 cases e;
 have e : x1 = A' := by
   sorry
 have ih1' := @ih1 (.type A' :: Γ') `★ B' t' sorry sorry sorry c3

 sorry

case _ =>
 sorry
case _ =>
 sorry
case _ =>
 sorry

-- implicits
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry


theorem compile_ctx_wf :
  CompileCtx Γ Γ' ->
  ⊢ Γ' := by
intro h2;
induction h2;
case _ => apply Judgment.wfnil
case _ ih1 =>
  case _ h1 =>
  apply Judgment.wfempty; assumption;
case _ h1 j1 cc ih =>
 apply Judgment.wfkind;
 sorry
 sorry
case _ => sorry
case _ => sorry
