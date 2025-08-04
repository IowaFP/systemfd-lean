import Hs.HsTerm
import Hs.Monad
import SystemFD.Term
import SystemFD.Judgment

import Hs.Translator.Kinds

theorem compile_kind_sound (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Γ ⊢ k' : c := by
intro wf e1 j;
induction c, k using compile_kind.induct generalizing k' <;> simp at *
case _ => cases j; constructor; assumption
case _ k1 k2 ih1 ih2 =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases e1;
  case _ e1 e2 =>
  replace ih1 := ih1 e1 h1;
  replace ih2 := ih2 e2 h2;
  constructor; assumption; assumption

theorem dsm_get_type_sound : ⊢ Γ ->
  DsM.toDsM s (Γ d@ h).get_type = .ok τ -> Γ ⊢ #h : τ := by
intro wf j
unfold DsM.toDsM at j
let gt := (Γ d@ h).get_type
generalize fh : Γ d@ h = f at *;
cases f;
all_goals try (
  simp at j;
  unfold Frame.get_type at j; simp at j
)
all_goals try (
  cases j; apply Judgment.var wf;
  unfold Frame.get_type; rw[fh]
)
