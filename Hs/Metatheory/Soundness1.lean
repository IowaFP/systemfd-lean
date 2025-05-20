import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import SystemFD.Algorithm.Soundness2

set_option maxHeartbeats 5000000

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
     apply Judgment.ax; assumption;
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

@[simp]
abbrev CompileCtxPred : (v : HsVariant) -> Prop
| .kind => ∀ Γ Γ' x T T',
  ⊢s Γ ->
  (Γ d@ x).get_type = .some T ->
  (j : Γ ⊢κ T : `□) ->
  compile .kind Γ ⟨(T, `□), j⟩ = .some T' ->
  (Γ' d@ x).get_type = .some T'
| .type =>
  ∀ Γ Γ' x k T T', ⊢s Γ ->
  (Γ d@ x).get_type = .some T ->
  (j : Γ ⊢τ T : k) ->
  compile .type Γ ⟨(T, k), j⟩ = .some T' ->
  (Γ' d@ x).get_type = .some T'
| .term =>
  ∀ Γ Γ' x T T' A, ⊢s Γ ->
  (Γ d@ x).get_type = .some T ->
  (j : Γ ⊢t T : A) ->
  compile .term Γ ⟨(T, A), j⟩ = .some T' ->
  (Γ' d@ x).get_type = .some T'
| .ctx => ∀ Γ (h1 h2 : ⊢s Γ), h1 = h2 -- needs fixing. Should ideally be coherence property i think


theorem compile_preserves_types :
  CompileCtxPred .kind ->
  ⊢ Γ' ->
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j2 : Γ ⊢κ k : `□) ->
  compile_kind Γ k `□ j2 = .some k' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  Γ' ⊢ τ' : k' := by
intro cc wf h j1 c1 j2 c2;
induction Γ, τ, k, j2 using compile_type.induct generalizing Γ' τ' k'
all_goals (unfold compile_type at c2; simp at c2)
case _ Γ T x wf' test gt j =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w c2 =>
  cases c2; case _ c2 e =>
  cases e;
  have lem := kinds_have_unique_judgments h j j1; cases lem;
  rw[c1] at c2; cases c2;
  simp at cc;
  have lem := @cc Γ Γ' x T k' wf' (Eq.symm gt) j c1; symm at lem;
  apply Judgment.var; assumption; assumption

case _ Γ B f A a  h1 h2 ja jb ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 c4 =>
  rw[Option.bind_eq_some] at c4;
  cases c4; case _ w3 c4 =>
  cases c4; case _ c4 c5 =>
  rw[Option.bind_eq_some] at c5;
  cases c5; case _ w4 c5 =>
  cases c5; case _ c5 e =>
  cases e;
  apply Judgment.appk;
  case _ =>
    have u := compile_kind_uniqueness h j1 jb c1 c3; cases u;
    have h' : compile_kind Γ (A `-k> B) `□ (ja.arrowk jb) = some (w1 -k> k') := by
      unfold compile_kind; simp;
      rw[Option.bind_eq_some];
      exists w1; apply And.intro
      case _ => assumption
      case _ => rw[Option.bind_eq_some]; simp; assumption
    have ih1' := @ih1 Γ' (w1 -k> k') w3 wf (HsJudgment.arrowk ja jb) h' c4
    apply ih1';
  case _ =>
    apply @ih2 Γ' w1 w4 wf ja c2 c5

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
  apply @ih1 (.kind w1 :: Γ') ★ w2 _ _ _ c3
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
  apply @ih1 Γ' ★ w1 wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl

  apply @ih2 (.empty::Γ') ★ w2 _ _ _ c3;
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
  apply @ih1 Γ' ★ w1 wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 (.empty::Γ') ★ w2 _ _ _ c3
  case _ => apply Judgment.wfempty; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl
