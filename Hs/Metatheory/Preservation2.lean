import Hs.Algorithm
import Hs.Metatheory.Uniqueness

import Aesop

set_option maxHeartbeats 500000

-- Says how the shape of the core context changes with Hs Ctx
@[aesop safe [constructors, cases]]
inductive CompileCtx : Ctx HsTerm -> Ctx Term -> Prop where
| nil : CompileCtx [] []
| empty :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  CompileCtx (.empty :: Γ) (.empty :: Γ')
| kind :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢κ A : `□) ->
  compile_kind Γ A `□ j1 = .some A' ->
  CompileCtx (.kind A :: Γ) (.kind A' :: Γ')
| type :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.type A :: Γ) (.type A' :: Γ')
| term :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★)  ->
  (j2 : Γ ⊢t t : τ) ->
  compile_type Γ A `★ j = .some A' ->
  compile_term Γ t τ j2 = .some t' ->
  CompileCtx (.term A t :: Γ) (.term A' t' :: Γ')

theorem compile_preserves_kinds :
  ⊢ Γ' ->
  (j : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j = .some t' ->
  Γ' ⊢ t' : .kind := by
 intro cc j c;
 induction Γ, t, τ, j using compile_kind.induct generalizing t'
 all_goals try (cases e)
 case _ =>
   unfold compile_kind at c; cases c;
   case _ =>
     apply Judgment.ax;
     assumption;
 case _ j1 j2 ih1 ih2 =>
   unfold compile_kind at c; simp at c;
   rw[Option.bind_eq_some] at c;
   cases c; case _ w1 c1 =>
   cases c1; case _ c1 c2 =>
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ w2 c2 =>
   cases c2; case _ c2 c3 =>
   cases c3;
   have ih1' := ih1 c1;
   have ih2' := ih2 c2;
   apply Judgment.allk;
   apply ih1';
   apply ih2'

def wf_ctx_well_kinded_types : ⊢s Γ -> (Γ d@ x).is_datatype -> (Γ d@ x).get_type = .some T ->  Γ ⊢κ T : `□ := sorry

def typing_implies_kinding : ∀ Γ, Γ ⊢τ τ : κ -> Γ ⊢κ κ : `□
| Γ, .varTy wf c gt => sorry
| Γ, .appk h _ => sorry
| Γ, .allt h _ =>  HsJudgment.ax (hs_judgment_ctx_wf .kind h)
| Γ, .arrow h _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)
| Γ, .farrow h _ _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)


theorem compile_preserves_types :
  CompileCtx Γ Γ' ->
  ⊢ Γ' ->
  (j2 : Γ ⊢κ k : `□) ->
  compile_kind Γ k `□ j2 = .some k' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  Γ' ⊢ τ' : k' := by
intro cc wf j1 c1 j2 c2;
induction Γ, τ, k, j2 using compile_type.induct generalizing Γ' τ' k'
all_goals (unfold compile_type at c2; simp at c2)
case _ Γ x wf test gt =>
     cases c2;
     apply Judgment.var;
     assumption;

     sorry
  -- apply compile_ctx_wf; assumption; assumption;
  -- have lem1 := HsJudgment.varTy wf test gt
  -- have lem := compile_preserves_type_indices cc lem1 c1; symm at lem;
  -- assumption
case _ B Γ f A a h1 h2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  apply Judgment.appk;
  case _ =>
    apply @ih1 Γ' _ w1 cc wf _ _ c2
    case _ => sorry
    case _ =>
      apply HsJudgment.arrowk;
      apply typing_implies_kinding Γ h2;
      assumption
    case _ => sorry
  case _ =>
    apply @ih2 Γ' _ w2 cc wf _ _ c3
    case _ => apply typing_implies_kinding Γ h2;
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
  apply compile_preserves_kinds wf h1 c2;
  apply @ih1 (.kind w1 :: Γ') ★ w2 _ _ _ _ c3
  case _ => apply CompileCtx.kind; assumption; assumption; assumption; assumption
  case _ => apply Judgment.wfkind; apply compile_preserves_kinds wf h1 c2; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfkind; assumption; assumption
  case _ => unfold compile_kind; rfl

case _ A B j1' j2' ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have lem1 := compile_preserves_kinds wf j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl

  apply @ih2 (.empty::Γ') ★ w2 _ _ _ _ c3;
  case _ => apply CompileCtx.empty; assumption; assumption; assumption
  case _ => apply Judgment.wfempty; assumption;
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
  have lem1 := compile_preserves_kinds wf j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  case _ tl1 tl2 _ =>
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 (.empty::Γ') ★ w2 _ _ _ _ c3
  case _ => apply CompileCtx.empty; assumption; assumption; assumption
  case _ => apply Judgment.wfempty; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl

theorem compile_preserves_terms :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  ⊢ Γ' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  (j2 : Γ ⊢t t : τ) ->
  compile_term Γ t τ j2 = .some t' ->
  Γ' ⊢ t' : τ' := by
intro h cc j1 c1 j2 c2;
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
 have uniq := types_have_unique_kinds j1 j3; subst uniq;
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
  ⊢s Γ ->
  (c : HsCtx Γ) ->
  compile_ctx c = .some Γ' ->
  ⊢ Γ' :=
by
intro h1 h2; sorry
-- induction h2;
-- case _ => apply Judgment.wfnil
-- case _ ih1 =>
--   case _ h1 =>
--   apply Judgment.wfempty; assumption;
-- case _ h1 j1 cc ih =>
--  apply Judgment.wfkind;
--  sorry
--  sorry
-- case _ => sorry
-- case _ => sorry
theorem compile_ctx_type : ∀ Γ Γ',
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (Γ d@ x).get_type = .some τ ->
  (j : Γ ⊢τ `#x : τ) ->
  compile_type Γ `#x τ j = .some τ' ->
  (Γ' @ x).get_type = .some τ' :=
by
intro Γ Γ' wf cc gt j c;
induction cc <;> simp at *;
case _ => cases gt
case _ ih1 =>
  induction x;
  case _ => simp at *; cases j; case _ j => cases j;
  case _ ih2 => simp; sorry
case _ => sorry
case _ => sorry
case _ => sorry
-- unfold compile_type at c; cases j; cases c;

theorem compile_preserves_term_indices :
  ⊢ Γ' ->
  (j1 : Γ ⊢t `#x : T) ->
  compile_type Γ T k j = .some T' ->
  (Γ' d@ x).get_type = .some T' := by
sorry
