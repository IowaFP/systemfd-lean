
import Hs.HsTerm
import Hs.Algorithm
import Hs.Monad

import SystemFD.Term
import Batteries.Lean.Except


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


theorem synth_coercion_type_sound : ⊢ Γ ->
  infer_kind Γ A = .some k ->
  infer_kind Γ B = .some k ->
  synth_coercion Γ A B = .some t -> Γ ⊢ t : (A ~[k]~ B) := by
intro wf jAk jBk j
induction Γ, A, B using synth_coercion.induct generalizing t k
all_goals (
  unfold synth_coercion at j; simp at j; rw[Option.bind_eq_some] at j
  cases j
)
case _ ih1 ih2 _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j;
  cases j; case _ j =>
  cases j; case _ j =>
  cases j;
  case _ w1 j1 w2 j2 =>
  unfold infer_kind at jAk; simp at jAk;
  rw[Option.bind_eq_some] at jAk; cases jAk; case _ jAk =>
  rw[Option.bind_eq_some] at jAk; cases jAk; case _ jAk =>
  cases jAk; case _ jAk =>
  rw[Option.bind_eq_some] at jAk; cases jAk; case _ jAk =>
  cases jAk; case _ jAk =>
  cases jAk; case _ jAk =>
  simp at jAk;
  cases jAk
  case _ A1k kk arrK _ B1k eA1 eA2 =>
  have lem := is_arrowk_some arrK;
  cases lem; unfold is_arrowk at arrK; simp at arrK;
  have lemA1 := infer_kind_sound A1k wf;
  cases eA2
  unfold infer_kind at jBk; simp at jBk;
  rw[Option.bind_eq_some] at jBk; cases jBk; case _ jBk =>
  rw[Option.bind_eq_some] at jBk; cases jBk; case _ jBk =>
  cases jBk; case _ jBk =>
  rw[Option.bind_eq_some] at jBk; cases jBk; case _ jBk =>
  cases jBk; case _ jBk =>
  cases jBk; case _ jBk =>
  simp at jBk; cases jBk;
  case _ A2k kk2 arr2K _ B2k eB1 eB2 =>
  have lem := is_arrowk_some arr2K;
  cases lem; unfold is_arrowk at arr2K; simp at arr2K;
  have lemA2 := infer_kind_sound A2k wf;
  have eq_lem : kk = kk2 := by
    sorry
  cases eq_lem
  have eq_kk1 := Term.eq_of_beq eA1
  have eq_kk2 := Term.eq_of_beq eB1
  cases eq_kk1; cases eq_kk2;
  replace ih1 := ih1 wf A1k A2k j1
  replace ih2 := ih2 wf B1k B2k j2
  apply Judgment.appc; assumption; assumption

· sorry
· sorry
· sorry


theorem synth_term_type_sound : ⊢ Γ ->
  synth_term n Γ τ = .some t -> Γ ⊢ t : τ := by
intro wf j
induction n, τ using synth_term.induct generalizing Γ t
all_goals (unfold synth_term at j)
· simp at j;
  cases j;
  case _ j =>
  sorry
· sorry
· sorry
case _ h =>
  unfold synth_term at j; simp at j; exfalso; simp_all;


theorem compile_type_sound (k : Term) (τ : HsTerm) :
  ⊢ Γ ->
  Term.IsKind k ->
  HsTerm.IsType τ ->
  compile_type Γ k τ = .ok τ' ->
  Γ ⊢ τ' : k := by
intro wf j1 j2 j
induction Γ, k, τ using compile_type.induct generalizing τ' <;> simp at *
case _ A B ih1 ih2 => -- a → b
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases j2;
  case _ e1 e2 =>
  have wf' := Judgment.wfempty wf
  replace ih1 := @ih1 w1 wf (by constructor) e1 h1
  replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
  constructor; assumption; assumption
case _ ih1 ih2 => -- a ⇒ b
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases j2;
  case _ e1 e2 =>
  have wf' := Judgment.wfempty wf
  replace ih1 := @ih1 w1 wf (by constructor) e1 h1
  replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
  constructor; assumption; assumption
case _ Γ A B ih => -- ∀[a] b
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases j2;
  case _ e1 e2 =>
  have lem := @compile_kind_sound Γ □ w1 A wf e1 h1
  have wf' := Judgment.wfkind lem wf
  replace ih := @ih w1 w2 wf' (by constructor) e2 h2
  constructor; assumption; assumption
case _ k τ tnf tnfp _ _ _ =>
  split at j; cases j
  case _ e => rw [tnfp] at e; cases e
case _ k τ sp h tnfp tnf _ _ _ ih =>
  split at j; cases j
  case _ e =>
  rw[tnf] at e; cases e;
  clear tnf; clear tnfp;
  split at j
  case _ he1 he2 =>
    cases he1; cases he2;
    rw[Except.bind_eq_ok] at j;
    cases j; case _ w1 j =>
    cases j; case _ t1 j =>
    simp at j
    rw[Except.bind_eq_ok] at j;
    cases j; case _ w2 j =>
    cases j; case _ t2 j =>
    split at j
    · rw[Except.bind_eq_ok] at j;
      cases j; case _ w3 j =>
      cases j; case _ t3 j =>
      cases j;
      have lem := dsm_get_type_sound wf t1;
      -- we are stuck here. as we do not know the shape of w1
      sorry
    · sorry

  case _ tnf ih =>
  rw[tnf] at e; cases e;
  have ih' := ih h e rfl; simp at ih'

case _ k τ tnf tnfp _ _ _ =>
  split at j;
  · cases j
  case _ h1 => rw[h1] at tnf; cases tnf; simp at j
