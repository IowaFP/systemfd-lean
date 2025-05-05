import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import Hs.Metatheory.TypeMatchCompile
import Hs.Metatheory.Soundness1
import Hs.Metatheory.Soundness2
import SystemFD.Algorithm.Soundness2

---------------------------------------------
-- Contexts
--------------------------------------------
theorem compile_preserves_ctx_shape Γ :
  ⊢s Γ -> (Η : HsCtx Γ) ->
  compile_ctx Η = .some Γ' ->
  (Γ d@ x).get_type = .some T ->
  (j : Γ ⊢κ T : `□) ->
  compile .kind Γ ⟨(T, `□), j⟩ = .some T' ->
  (Γ' d@ x).get_type = .some T'
 := by
intro wf h cc gt j ck;
induction h generalizing Γ';
case _ => cases gt
case _ Γ h ih =>
  cases wf; case _ wf =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ wΓ cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ u cc1 =>
  cases cc1; case _ cc1 e =>
  cases e;
  have ih' := @ih wΓ wf cc
  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry


theorem compile_preserves_wf Γ :
  ⊢s Γ -> (Η : HsCtx Γ) -> compile_ctx Η = .some Γ' -> ⊢ Γ' := by
intro wf h cc;
induction h generalizing Γ';
case _ =>
  unfold compile_ctx at cc; cases cc;
  apply Judgment.wfnil;
case _ ih =>
  cases wf; case _ wf =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  cases cc2;
  apply Judgment.wfempty;
  apply wf_ctx_sound cc1;
case _ j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ w2 cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  apply Judgment.wfkind;
  apply compile_preserves_kinds _ j cc2;
  case _ => apply @ih w wf cc
  apply @ih w wf cc
case _ j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ w2 cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  apply Judgment.wfdatatype;
  apply compile_preserves_kinds _ j cc2;
  case _ => apply @ih w wf cc
  apply @ih w wf cc
case _ Γ τ a j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ Γ' cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ τ' cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  have lem := @ih Γ' wf cc
  have lemAx : Γ ⊢κ `★ : `□ := by apply HsJudgment.ax (hs_judgment_ctx_wf .type jk)
  have lemK : compile_kind Γ `★ `□ lemAx = .some ★ := by unfold compile_kind; cases lemAx; simp
  apply Judgment.wftype;
  apply compile_preserves_types _ lem _ lemAx lemK j cc2;
  case _ =>
    simp;
    intros Γ Γ' x T T' wf gt j ck;
    unfold compile at ck; simp at ck; sorry
  case _ => intros; sorry
  assumption

case _ ih =>
  cases wf; case _ wf j vhv =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ Γ' cc =>
  cases cc; case _ ca cc =>
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ w' cc =>
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ τ' cc =>
  cases cc; case _ cτ cc =>
  cases cc
  constructor;
  sorry
  case _ =>
    apply ih;
    assumption
    assumption
  sorry
case _ => sorry
case _ => sorry
