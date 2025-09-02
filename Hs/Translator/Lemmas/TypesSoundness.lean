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
case _ =>
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
        cases j3; case _ Γ _ τ sp _ _ _ _ _ _ _ j3 =>
        case _ w1 _ sp_τs =>
        apply Term.mk_kind_app_rev_is_type
        have lem := HsTerm.hs_type_neutral_form_is_type τ j1 tnfp
        cases lem; case _ _ _ _ _ _ lem1 lem2 =>
        constructor
        constructor
        case _ head_κ =>
          intro τ τs_in_sp_τs
          generalize fh : (λ (arg : {q // q ∈ (κs.attach).zip (sp.attach)}) =>
                    if
            (match arg.val.snd.val.fst, HsSpineVariant.kind with
              | HsSpineVariant.term, HsSpineVariant.term => true
              | HsSpineVariant.kind, HsSpineVariant.kind => true
              | HsSpineVariant.type, HsSpineVariant.type => true
              | x, x_1 => false) =
              true then
          compile_type Γ arg.val.fst.val arg.val.snd.val.snd
          else Except.error (Std.Format.text "compile_type ill kinded ty arg" ++ repr arg.val)) = f at *

          have lem3 := mapM'_elems ((κs.attach.zip sp.attach).attach) sp_τs f;
          rw[List.mapM'_eq_mapM] at lem3
          rw[<-fh] at lem3;
          replace lem3 := lem3 h2
          simp at lem3
          have lem4 := mapM'_elems_length ((κs.attach.zip sp.attach).attach) sp_τs f
          rw[<-fh] at lem4;
          rw[<-List.mapM'_eq_mapM] at h2
          replace lem4 := lem4 h2
          induction κs generalizing sp
          case _ =>
            simp at h1; simp at lem4
            have lem5 := list_empty_length sp_τs (Eq.symm lem4)
            cases lem5; simp at τs_in_sp_τs
          case _ κh κs ih1 _ =>
          induction sp <;> simp at h1
          case _ sph sps _ _ =>
          unfold List.zip at h2;
          unfold List.mapM' at h2; simp at h2;
          generalize zzh : (List.zipWith Prod.mk (κh :: κs).attach (sph :: sps).attach).attach = zz at *
          cases zz <;> simp at h2
          case _ =>
            unfold pure at h2; unfold Applicative.toPure at h2; unfold Monad.toApplicative at h2;
            unfold Except.instMonad at h2; unfold Except.pure at h2; simp at h2; cases h2; simp at τs_in_sp_τs
          case _ =>

            unfold bind at h2; unfold Monad.toBind at h2; unfold Except.instMonad at h2; simp at h2;
            cases h2; case _ hd h2 =>
            simp at h2; cases h2
            case _ hd hd' tl h2a h2b =>

            simp at h2a;
            cases hd'; case _ hdv hdp =>
            cases hdv; case _ hdv1 hdv2 =>
            cases hdv2; case _ hdv2v hdv2p =>
            simp at h2a
            cases hdv2v; case _ hdv2v1 hdv2v2 =>
            cases hdv2v1 <;> simp at h2a
            unfold Except.map at h2b
            split at h2b <;> simp at h2b
            cases h2b; simp at lem4
            have ih := ih  (κh :: κs) κh (by simp) .kind sph.snd (by sorry) (by sorry) τ wf
            sorry

          -- have ih1' := ih1 (sph :: sps) tnfp tnfp ih
          -- let spp := sp.attach
          -- let κsp := κs.attach
          -- induction κs.zip sp;
          -- sorry;
          -- assumption

          -- let ih' := λ (a : Term) (spv : List (HsSpineVariant × HsTerm)) (b : HsTerm) => ih κs a

          -- have h2' := forget_attach h2
          -- have lem4 := lem3 h2'

       case _ => cases j3
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
