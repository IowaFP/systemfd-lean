import Hs.HsTerm
import Hs.Monad
import Hs.Translator.Lemmas.KindSoundness
import Hs.Translator.Lemmas.Utils

import Hs.Translator.HsTerm
import Hs.SynthInstance

import SystemFD.Term
import SystemFD.Metatheory.Inversion

import Batteries.Lean.Except


theorem compile_type_shape_soundness (Γ : Ctx Term) (k : Term) (τ : HsTerm) (τ' : Term): ⊢ Γ ->
 HsTerm.IsType τ ->
 Term.IsKind k ->
 compile_type Γ k τ = .ok τ' ->
 Term.IsType Γ τ' := by
intro wf j1 j2 j3
induction Γ, k, τ using compile_type.induct generalizing τ' <;> simp at *

all_goals try (
case _ ih1 ih2 =>
  cases j3; case _ j3 =>
  cases j3; case _ j3 =>
  cases j3; cases j1; case _ h1 _ h2 h3 h4 =>
  cases h2; case _ A' B' h2 e =>
  cases e
  have ih1' := ih1 A' wf h3 (by constructor) h1
  replace ih2 := ih2 B' (Judgment.wfempty wf) h4 (by constructor) h2
  constructor; assumption; assumption)

case _ Γ K A ih =>
  cases j3; case _ j3 =>
  cases j3; case _ j3 =>
  cases j3; cases j1; case _ K' h1 A' h2 h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  have lem' : Except.ok K' = DsM.ok K' := by simp
  rw[lem'] at h1;

  have lem := @compile_kind_sound Γ □ K' K wf h3 h1
  have wf' : ⊢ (.kind K' :: Γ) := by constructor; assumption; assumption
  replace ih := @ih K' A' wf' h4 (by constructor) h2
  have lem := kind_shape lem rfl
  constructor; assumption; assumption

case _ tnf _ _ _ => simp_all; rw[tnf] at j3; simp at j3
case _ =>
 simp_all;
 case _ tnfp _ _ _ _ =>
 split at j3
 case _ => cases j3
 case _ =>
   split at j3
   case _ =>
     rw[Except.bind_eq_ok] at j3; cases j3; case _ j3 =>
     cases j3; case _ j3 =>
     simp at j3;
     split at j3
     case _ => cases j3
     case _ =>
       split at j3
       case _ =>
        rw[Except.bind_eq_ok] at j3; cases j3; case _ j3 =>
        cases j3; case _ ih _ _ tnfp' _ tnfp'' _ _ κs ret_κ j4 h1 _ h2 j3 =>
        rw[tnfp] at tnfp'; cases tnfp';rw[tnfp] at tnfp''; cases tnfp''
        simp at h1; cases h1; case _ h1' h1 =>
        cases h1'; case _ h1' h1'' =>
        replace h1' := Term.eq_of_beq h1'; cases h1'
        cases j3; case _ τ sp _ _ _ _ _ _ j3 =>
        case _ w1 _ sp_τs =>
        apply Term.mk_kind_app_rev_is_type
        have lem := HsTerm.hs_type_neutral_form_is_type τ j1 tnfp
        cases lem; case _ Γ _ _ _ _ _ lem1 lem2 =>
        constructor
        constructor; sorry
        intro ki
        have lem3 := mapM'_elems (κs.zip sp) sp_τs (λ a => compile_type Γ a.1 a.2.2);
        rw[List.mapM'_eq_mapM] at lem3

        sorry
       case _ => cases j3
   case _ => cases j3
case _ tnf _ _ _ _ => simp_all; rw[tnf] at j3; simp at j3;


theorem synth_coercion_type_sound : ⊢ Γ ->
  Term.isType Γ A ->
  Term.isType Γ B ->
  infer_kind Γ A = .some k ->
  infer_kind Γ B = .some k ->
  synth_coercion Γ A B = .some t ->
  Γ ⊢ t : (A ~[k]~ B) := by
intro wf wflhs wfrhs jlhsk jrhsk j
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
  unfold infer_kind at jlhsk; simp at jlhsk;
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  simp at jlhsk;
  cases jlhsk
  case _ A1k kk arrK _ B1k eA1 eA2 =>
  have lem := is_arrowk_some arrK;
  cases lem; unfold is_arrowk at arrK; simp at arrK;
  have lemA1 := infer_kind_sound A1k wf;
  cases eA2
  unfold infer_kind at jrhsk; simp at jrhsk;
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  simp at jrhsk; cases jrhsk;
  case _ A2k kk2 arr2K _ B2k eB1 eB2 =>
  have lem := is_arrowk_some arr2K;
  cases lem; unfold is_arrowk at arr2K; simp at arr2K;
  have lemA2 := infer_kind_sound A2k wf;
  cases j3; cases j4; clear jes;
  replace eB1 := Term.eq_of_beq eB1;
  replace eA1 := Term.eq_of_beq eA1;
  cases eB1; cases eA1;
  unfold Term.isType at wflhs; simp at wflhs;
  unfold Term.isType at wfrhs; simp at wfrhs;
  cases wflhs; cases wfrhs;
  simp_all;
  apply Judgment.appc; assumption; assumption

case _ ih1 ih2 _ j => -- A1 -t> B1 ~ A2 -t> B2
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j
  case _ kA1 jA1 kA2 jA2 kB1 jB1 kB2 jB2 jes w1 j1 w2 j2 =>
  have j3 := Term.eq_of_beq jes.1
  have j4 := Term.eq_of_beq jes.2
  cases j3; cases j4; clear jes
  have jAk' := infer_kind_sound jlhsk wf
  have jrhsk' := infer_kind_sound jrhsk wf
  cases jAk'; cases jrhsk'
  unfold Term.isType at wflhs; simp at wflhs
  unfold Term.isType at wfrhs; simp at wfrhs
  case _ jA1k jB1k jA2k jB2k =>
  have lemA1k := infer_kind_sound jA1 wf
  have lemB1k := infer_kind_sound jB1 (Judgment.wfempty wf)
  have lemA2k := infer_kind_sound jA2 wf
  have lemB2k := infer_kind_sound jB2 (Judgment.wfempty wf)
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.1) lemA1k jA1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.1) lemA1k jA1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.2) lemB1k jB1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wfrhs.2) lemB2k jB2k; cases u
  have ih1' := @ih1 ★ w1 wf wflhs.1 wfrhs.1 jA1 jA2 j1
  have ih2' := @ih2 ★ w2 (Judgment.wfempty wf) wflhs.2 wfrhs.2 jB1 jB2 j2
  constructor; assumption;  assumption

case _ K1 _ _ _ ih _ j => -- Γ ⊢ t : ((∀[K1]A1) ~[k]~ ∀[K2]A2)
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  cases j; case _  j1 _ j2 _ j3 _ j4 j5 w j6 =>
  replace j5 := Term.eq_of_beq j5; cases j5
  have j1' := wf_kind_sound j1 wf
  clear j2;
  have lem' := infer_kind_sound jrhsk wf
  cases lem'; case _ lemlhs =>
  have lem' := infer_kind_sound jlhsk wf
  cases lem'; case _ lemrhs =>
  have wf' := Judgment.wfkind j1' wf
  unfold Term.isType at wflhs; simp at wflhs
  unfold Term.isType at wfrhs; simp at wfrhs
  have lemA1 := infer_kind_sound j3 (Judgment.wfkind j1' wf)
  have lemA2 := infer_kind_sound j4 (Judgment.wfkind j1' wf)
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.2) lemrhs lemA1; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wfrhs.2) lemlhs lemA2; cases u
  case _  jB1k _ jB2k =>
  have ih1' := @ih ★ w (Judgment.wfkind j1' wf) wflhs.2 wfrhs.2 j3 j4 j6
  constructor; assumption; assumption

case _ j =>
 cases j; case _ j =>
 simp at j; split at j
 · cases j; case _ j =>
   replace j := Term.eq_of_beq j; cases j
   case _ k jlhs _ _ _ =>
   rw[jlhs] at jrhsk; cases jrhsk
   constructor
   · have lem1 := infer_kind_sound jlhsk wf;
     have lem3 := kind_of_type_well_formed wf lem1; simp at lem3;
     replace lem3 := lem3 wflhs lem1;
     assumption
   · apply infer_kind_sound jlhs wf
 · rw[Option.bind_eq_some] at j; cases j; case _ j =>
   cases j; case _ j1 j2 => sorry -- needs coercion_graph_kind_soundness etc.


theorem synth_term_type_sound : ⊢ Γ ->
  Term.isType Γ τ ->
  Term.isKind k ->
  Γ ⊢ τ : k ->
  synth_term n Γ τ = .some t ->
  Γ ⊢ t : τ := by
intro wf wfτ wfk jk j
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
    unfold Term.isType at wfτ; simp at wfτ;
    cases wfτ; case _ wfτ _ =>
    cases wfτ; cases jk;
    case _ j1 _ j2 j3 j4 j5 j6 j7 j8 =>
    have lemA := infer_kind_sound j1 wf
    have lemB := infer_kind_sound j2 wf
    have lemA' := Term.is_type_shape_sound j4
    have lemB' := Term.is_type_shape_sound j5
    have u := uniqueness_of_kinds lemA' j7 lemA; cases u
    have u := uniqueness_of_kinds lemB' j8 lemB; cases u
    apply synth_coercion_type_sound; assumption; assumption; assumption; assumption; assumption; assumption
· simp at j;
  cases j;
  case _ ih1 ih2 _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j;
  case _ e _ =>
  replace e := Term.eq_of_beq e; cases e;
  case _ j _ =>
  split at j
  case _ => cases j; sorry
  case _ =>
    sorry
case _ h =>
  unfold synth_term at j; simp at j; exfalso; simp_all;
  cases j; case _ j =>
  simp at j;
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j1 j2 =>
  sorry
case _ => simp_all -- contradiction case we are out of corns


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
    simp at j; split at j;
    case _ => cases j
    case _ =>
      split at j
      · rw[Except.bind_eq_ok] at j;
        cases j; case _ w3 j =>
        cases j; case _ t3 j =>
        cases j;
        simp_all
        cases e; case _ κs ret_k tnf j3 j4 =>
        cases j4; case _ j4 _ =>
        cases j4; case _ j4 j5 =>
        have e := Term.eq_of_beq j4; cases e; clear j4
        induction κs
        case _ j4 =>
          simp at j4; sorry
        case _ => sorry
      cases j

  case _ tnf ih =>
  rw[tnf] at e; cases e;
  have ih' := ih h e rfl; simp at ih'

case _ k τ tnf tnfp _ _ _ =>
  split at j;
  · cases j
  case _ h1 => rw[h1] at tnf; cases tnf; simp at j
