
import Hs.HsTerm
import Hs.Monad
import Hs.Translator.Lemmas.KindSoundness

import Hs.Translator.HsTerm
import Hs.SynthInstance

import SystemFD.Term
import Batteries.Lean.Except


theorem synth_coercion_type_sound : ⊢ Γ ->
  Term.IsType A ->
  Term.IsType B ->
  infer_kind Γ A = .some k ->
  infer_kind Γ B = .some k ->
  synth_coercion Γ A B = .some t -> Γ ⊢ t : (A ~[k]~ B) := by
intro wf wfA wfB jAk jBk j
induction Γ, A, B using synth_coercion.induct generalizing t k
all_goals (
  unfold synth_coercion at j; simp at j; rw[Option.bind_eq_some] at j
  cases j
)
case _ ih1 ih2 _ j => -- A1 `@k B1 ~ A2 `@k B2
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j;
  case _ kA1 jA1 kA2 jA2 kB1 jB1 kB2 jB2 jes w1 j1 w2 j2 =>
  have j3 := Term.eq_of_beq jes.1
  have j4 := Term.eq_of_beq jes.2
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
  cases j3; cases j4; clear jes;
  replace eB1 := Term.eq_of_beq eB1;
  replace eA1 := Term.eq_of_beq eA1;
  cases eB1; cases eA1;
  cases wfA; cases wfB;
  case _ h1 h2 _ _ h3 h4 =>
  have ih1' := @ih1 (kk.fst -k> kk.snd) w1 wf h1 h3

  simp_all;
  apply Judgment.appc; sorry; sorry; sorry

· sorry -- A1 -t> B1 ~ A2 -t> B2
· sorry
case _ j =>
 cases j; case _ j =>
 simp at j; split at j
 · cases j; case _ j =>
   replace j := Term.eq_of_beq j; cases j
   case _ k jlhs _ _ _ =>
   rw[jlhs] at jBk; cases jBk
   constructor
   · have lem := infer_kind_sound jAk wf;

     sorry
   · apply infer_kind_sound jlhs wf
 · rw[Option.bind_eq_some] at j; cases j; case _ j =>
   cases j; case _ j1 j2 => sorry -- needs coercion_graph_kind_soundness etc.


theorem synth_term_type_sound : ⊢ Γ ->
  Γ ⊢ τ : k ->
  synth_term n Γ τ = .some t -> Γ ⊢ t : τ := by
intro wf jk j
induction n, τ using synth_term.induct generalizing Γ t
all_goals (unfold synth_term at j)
· simp at j;
  cases j;
  case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j;
  case _ e _ =>
  replace e := Term.eq_of_beq e; cases e;
  case _ =>
  apply synth_coercion_type_sound; assumption; sorry; sorry; sorry
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
