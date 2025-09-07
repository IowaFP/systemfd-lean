import Hs.HsTerm
import Hs.Monad
import Hs.Translator.Lemmas.KindSoundness
import Hs.Translator.Lemmas.Utils

import Hs.Translator.HsTerm
import Hs.SynthInstance

import SystemFD.Term
import SystemFD.Metatheory.Inversion

import Batteries.Lean.Except

theorem is_type_list_reverse (τs : List Term) :
  (∀ τ ∈ τs, Term.IsType τ) -> ∀ τ ∈ τs.reverse, Term.IsType τ := by
  intro h t h2
  have lem : t ∈ τs := by simp at h2; assumption
  replace h := h t lem
  assumption


theorem is_type_spine_application' (τh : Term) (τs : List Term) :
  τh.IsType ->
  (∀ τ ∈ τs, Term.IsType τ) ->
  Term.IsType (τh.mk_kind_apps' τs) := by
intro h1 h2; simp at *
induction τs using List.foldr.induct <;> simp at *
case _ => assumption
case _ ih =>
  cases h2; case _ h2a h2b =>
  constructor;
  replace ih := ih h2b; assumption
  assumption


theorem is_type_spine_application (τh : Term) (τs : List Term) :
  τh.IsType ->
  (∀ τ ∈ τs, Term.IsType τ) ->
  Term.IsType (τh.mk_kind_apps τs) := by
intro h1 h2
have lem := is_type_list_reverse τs h2
unfold Term.mk_kind_apps
apply is_type_spine_application'
assumption
assumption

theorem compile_type_shape_soundness (Γ : Ctx Term) (k : Term) (τ : HsTerm) (τ' : Term): ⊢ Γ ->
 HsTerm.IsType τ ->
 Term.IsKind k ->
 compile_type Γ k τ = .ok τ' ->
 Term.IsType τ' := by
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
case _ sp idx _ tnfp _ _ _ _ =>
 split at j3
 case _ => cases j3
 case _ =>
 split at j3
 /- head is a variable -/
 case _ =>
  simp at j3; cases j3; case _ n tnfp idx tnfp' κ j3 =>
  rw[tnfp] at tnfp'; cases tnfp'
  case _ tnfp' tnfp'' _ _ _ _ _ =>
  rw[tnfp] at tnfp'; cases tnfp'; clear tnfp''
  cases j3; case _ j3 =>
  split at j3
  case _ => /- bogus case -/ simp at j3
  case _ κs ret_κ j4 =>
  split at j3;
  case _ =>
    rw[Except.bind_eq_ok] at j3; cases j3
    case _ j5 τs j3 =>
    simp at j5; cases j5; case _ j6 j5 =>
    cases j6; case _ j6 j7 =>
    have e := Term.eq_of_beq j6; cases e; clear j6
    cases j3; case _ exp_κ τ _ _ _ _ _ j3 j6 =>
    cases j6;
    have lem1 := HsTerm.hs_type_neutral_form_is_type j1 tnfp
    have lem2 := HsTerm.hs_is_type_neutral_form j1 tnfp
    cases lem1; case _ lem1a =>
    -- have κ_wf : κ.IsKind := by sorry
    -- have lem3 := kind_shape_split_arrow κ_wf j4
    -- cases lem3; case _ lem3a lem3b =>
    rw[List.foldl_eq_foldr_reverse]
    apply is_type_spine_application
    case _ => constructor
    case _ ih _ _ =>
      intro sp_τ τ_in_sp
      induction [], κ using Term.split_kind_arrow_aux.induct <;> simp at j4
      sorry
      -- have ih' := ih κs
      case _ =>
        cases j4.1; cases j4.2; simp at j3; cases j3; cases τ_in_sp

    -- generalize zzh : κs.attach.zip sp.attach = zz at *
    -- induction κs generalizing sp <;> simp at zzh
    -- case _ =>
    --   cases zzh
    --   simp at j3; unfold pure at j3; unfold Applicative.toPure at j3;
    --   unfold Monad.toApplicative at j3; unfold Except.instMonad at j3; simp at j3;
    --   unfold Except.pure at j3; simp at j3; cases j3; simp; constructor
    -- case _ κhd κtl _ _ =>
    --   induction sp <;> simp at zzh
    --   case _ =>
    --     cases zzh
    --     simp at j3; unfold pure at j3; unfold Applicative.toPure at j3;
    --     unfold Monad.toApplicative at j3; unfold Except.instMonad at j3; simp at j3;
    --     unfold Except.pure at j3; simp at j3; cases j3; simp; constructor
    --   case _ sph sptl _ _ =>
    --     rw[<-zzh] at j3; rw[<-List.mapM'_eq_mapM] at j3
    --     simp at j3
    --     unfold bind at j3; unfold Monad.toBind at j3; unfold Except.instMonad at j3; simp at j3
    --     cases j3; case _ j3 =>
    --     cases j3; case _ j3a j3b =>
    --     simp at j3a; simp at j3b
    --     unfold Except.map at j3b; split at j3b <;> simp at j3b
    --     cases j3b; rw[List.foldl_eq_foldr_reverse]; sorry





  case _ => cases j3
 /- head is a not a variable, bogus case -/
 case _ => cases j3
case _ tnf _ _ _ _ => simp_all; rw[tnf] at j3; simp at j3;


theorem compile_type_sound (k : Term) (τ : HsTerm) :
  ⊢ Γ ->
  Term.IsKind k ->
  HsTerm.IsType τ ->
  compile_type Γ k τ = .ok τ' ->
  Γ ⊢ τ' : k := by
intro wf j1 j2 j
induction Γ, k, τ using compile_type.induct generalizing τ' <;> simp at *
case _ A B ih1 ih2 => -- a → b
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases j2;
  case _ e1 e2 =>
  have wf' := Judgment.wfempty wf
  replace ih1 := @ih1 w1 wf (by constructor) e1 h1
  replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
  constructor; assumption; assumption
case _ ih1 ih2 => -- a ⇒ b
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases j2;
  case _ e1 e2 =>
  have wf' := Judgment.wfempty wf
  replace ih1 := @ih1 w1 wf (by constructor) e1 h1
  replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
  constructor; assumption; assumption
case _ Γ A B ih => -- ∀[a] b
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
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
        case _ j =>
        simp at j; cases j; case _ j3 j4 =>
        cases j3; case _ j3 j5 =>
        have e := Term.eq_of_beq j3; cases e; clear j3

        sorry
      cases j

  case _ tnf ih =>
  rw[tnf] at e; cases e;
  have ih' := ih h e rfl; simp at ih'

case _ k τ tnf tnfp _ _ _ =>
  split at j;
  · cases j
  case _ h1 => rw[h1] at tnf; cases tnf; simp at j
