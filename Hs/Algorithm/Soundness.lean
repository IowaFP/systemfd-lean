import Hs.HsTerm
import Hs.Algorithm
import Hs.HsJudgment
import Hs.CompileJ

set_option maxHeartbeats 500000

@[simp]
abbrev KindLike : Term -> Prop
| _ -k> _ => true
| ★ => true
| _ => false

inductive HsKindLike : HsTerm -> Prop where
| HsType : HsKindLike `★
| HsArrK : HsKindLike k1 -> HsKindLike k2 -> HsKindLike (k1 `-k> k2)


theorem compile_soundness_kinds :
  HsKindLike t ->
  τ = `□ ->
  (j : Γ ⊢s t : τ) ->
  compile Γ t τ j = .some t' ->
  CompileKind t t' := by
intro h e j c;
induction Γ, t, τ, j using compile.induct generalizing t'
case _ =>
  unfold compile at c; cases c;
  apply CompileKind.type;
case _ j1 j2 ih1 ih2 =>
  unfold compile at c; simp at c;
  rw[Option.bind_eq_some] at c;
  cases c; case _ t1' c1 =>
  cases c1; case _ c1 c =>
  rw[Option.bind_eq_some] at c;
  cases c; case _ t2' c2 =>
  cases c2; case _ c2 t3 =>
  cases t3; cases h;
  case _ h1 h2 =>
  apply CompileKind.arrowk;
  apply ih1 h1 rfl c1;
  apply ih2 h2 rfl c2;
all_goals (cases h)
all_goals try (cases e)
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry

-- theorem compile_soudness :
--   (j : Γ ⊢s t : τ) ->
--   compile Γ t τ j = .some t' ->
--   (∃ idx, CompileJ .kind Γ idx) ∨ (∃ idx, CompileJ .type Γ idx) ∨ (∃ idx, CompileJ .term Γ idx) := by
-- intro j c;
-- induction Γ, t, τ, j using compile.induct generalizing t' <;> (unfold compile at c; simp at c)
-- case _ wf =>
--   apply Or.inl;
--   exists ⟨`★, `□; HsJudgment.ax wf, ★⟩
--   apply CompileJ.type;
-- case _ A B Aj Bj ih1 ih2 =>
--   rw [Option.bind_eq_some] at c;
--   cases c; case _ t1 c =>
--   cases c; case _ c1 c2 =>
--   rw [Option.bind_eq_some] at c2;
--   cases c2; case _ t2 c2 =>
--   cases c2; case _ c2 t3 =>
--   cases t3;
--   apply Or.inl; exists ⟨A `-k> B, `□; HsJudgment.arrowk Aj Bj, t1 -k> t2⟩
--   apply CompileJ.arrowk
--   case _ => have ih1' := ih1 c1; simp at ih1'; sorry
--   sorry
--   assumption
--   assumption
-- case _ j _ _ _ j1 j2 =>
--   sorry
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
