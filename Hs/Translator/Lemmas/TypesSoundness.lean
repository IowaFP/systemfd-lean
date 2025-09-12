import Hs.HsTerm
import Hs.Monad
import Hs.Translator.Lemmas.KindSoundness
import Hs.Translator.Lemmas.Utils

import Hs.Translator.HsTerm
import Hs.SynthInstance

import SystemFD.Term
import SystemFD.Metatheory.Inversion

import Batteries.Lean.Except

-- import Aesop

theorem is_type_list_reverse (τs : List Term) :
  (∀ τ ∈ τs, Term.IsType τ) -> ∀ τ ∈ τs.reverse, Term.IsType τ := by
  intro h t h2
  have lem : t ∈ τs := by simp at h2; assumption
  replace h := h t lem
  assumption

theorem hs_is_type_list_reverse (τs : List HsTerm) :
  (∀ τ ∈ τs, HsTerm.IsType τ) -> ∀ τ ∈ τs.reverse, HsTerm.IsType τ := by
  intro h t h2
  have lem : t ∈ τs := by simp at h2; assumption
  replace h := h t lem
  assumption


theorem hs_is_type_spine_application' (τh : HsTerm) (τs : List HsTerm) :
  τh.IsType ->
  (∀ τ ∈ τs, HsTerm.IsType τ) ->
  HsTerm.IsType (τh.mk_kind_apps' τs) := by
intro h1 h2; simp at *
induction τs using List.foldr.induct <;> simp at *
case _ => assumption
case _ ih =>
  cases h2; case _ h2a h2b =>
  constructor;
  replace ih := ih h2b; assumption
  assumption


theorem hs_is_type_spine_application (τh : HsTerm) (τs : List HsTerm) :
  τh.IsType ->
  (∀ τ ∈ τs, HsTerm.IsType τ) ->
  HsTerm.IsType (τh.mk_kind_apps τs) := by
intro h1 h2
have lem := hs_is_type_list_reverse τs h2
unfold HsTerm.mk_kind_apps
apply hs_is_type_spine_application'
assumption
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

theorem kind_split_mk_arrow_aux {Γ : List Term} {κs : List Term} {k : Term}:
  k.split_kind_arrow_aux Γ = .some (κs, ret_κ) ->
  ∃ κs', κs = κs' ++ Γ := by
 intro h
 induction Γ, k using Term.split_kind_arrow_aux.induct generalizing κs ret_κ <;> simp at h
 case _ f a ih =>
   have ih' := ih h
   cases ih'; case _ w e =>
   exists (w ++ [f])
   rw[e]; simp
 cases h.1; cases h.2; exists []

theorem kind_split_empty_κs :
  Term.split_kind_arrow_aux [] k = some ([], ret_κ) ->
  k = ret_κ := by
intro h
induction [], k using Term.split_kind_arrow_aux.induct generalizing ret_κ <;> simp at h
case _ =>
 exfalso
 have lem := kind_split_mk_arrow_aux h
 cases lem; case _ lem => simp at lem
assumption

theorem typing_spine_application' {Γ : Ctx Term} {n : Nat} {τs : List Term} {k : Term}:
  Γ ⊢ k : □ ->
  Γ ⊢ #n : k ->
  k.split_kind_arrow = .some (κs, ret_κ) ->
  κs.length = τs.length ->
  d = κs.zip τs ->
  (∀ (p : i < d.length), Γ ⊢ (d[i].2) : (d[i].1) ) ->
  Γ ⊢ ((#n).mk_kind_apps' τs) : ret_κ := by
intro j1 j2 h1 h2 h3 j3;
have wf := judgment_ctx_wf j1
have lem := kinding_split_arrow wf j1 h1
induction d using List.foldr.induct generalizing k κs τs <;> simp at *
case _ =>
  cases h3
  case _ e =>
    -- cases e; cases lem; case _ lem => simp at lem; sorry
    cases e; simp at h2; symm at h2; replace h2 := list_empty_length h2; cases h2; simp;
    have lem1 := kind_split_mk_arrow_aux h1; simp at lem;
    cases lem1; case _ lem1 =>
    simp at lem1; cases lem1
    have lem1 := kind_split_empty_κs h1; subst lem1; assumption
  case _ e =>
    cases e; simp; simp at h2; cases h2;
    have lem1 := kind_split_empty_κs h1; subst lem1; assumption
case _ ih =>
 have lem1 : ∃ κshd κstl, κs = (.cons κshd κstl) := by
   sorry
 have lem2 : ∃ τshd τstl, τs = (.cons τshd τstl) := by
   sorry
 cases lem1; case _ κshd lem1 =>
 cases lem1; case _ κstl lem1 =>
 cases lem2; case _ τshd lem2 =>
 cases lem2; case _ τstl lem2 =>
 cases lem1; cases lem2
 unfold Term.split_kind_arrow_aux at h1;
 split at h1 <;> try simp at h1
 case _ =>
    simp at h2
    sorry


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
   rw[tnfp] at tnfp'; cases tnfp'; clear tnfp''; cases j3; case _ j4 j3 =>
   simp at j3; split at j3
   case _ wfk =>
     split at j3
     case _ => simp at j3
     case _ κs ret_κ h1 =>
     split at j3
     case _ j4 =>
       simp at j4
       cases j4; case _ j4 j5 =>
       cases j4; case _ j4 j6 =>
       have e := Term.eq_of_beq j4; cases e; clear j4
       rw[Except.bind_eq_ok] at j3; cases j3
       case _ exp_κ τ _ _ _ ih τs j3 =>
       cases j3; case _ j3 j7 =>
       cases j7; rw[List.foldl_eq_foldr_reverse]
       have lem1 := HsTerm.hs_type_neutral_form_is_type j1 tnfp
       have lem2 := HsTerm.hs_is_type_neutral_form j1 tnfp
       rw[<-List.mapM'_eq_mapM] at j3

       cases lem1; case _ lem1a =>
       have κ_wf : κ.IsKind := wf_kind_shape_sound wfk
       have lem3 := kind_shape_split_arrow κ_wf h1
       cases lem3; case _ lem3a lem3b =>
       apply is_type_spine_application
       case _ => constructor
       case _ ih _ _ =>
         intro τ' τ'_in_τs
         have lem3 := mapM'_elems_image j3 τ' τ'_in_τs
         cases lem3; case _ lem3 =>
         cases lem3; case _ w w_in_sp lem3 =>
         simp at lem3; split at lem3 <;> simp at lem3
         case _ contra => simp at contra
         case _ e _ =>
           have lem2' := lem2 (w.val.snd.val.fst, w.val.snd.val.snd) w.val.snd.property
           simp at lem2'; cases lem2'
           apply ih κs w.val.fst w.val.fst.property (w.val.snd.val.fst) _ _ _ τ' wf _ _ lem3
           apply w.val.snd.property
           apply w.property
           assumption
           apply lem3b w.val.fst.val w.val.fst.property
         case _ contra => simp at contra

     case _ => simp at j3
   case _ => simp at j3

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
  have lem1 := @compile_kind_sound Γ □ w1 A wf e1 h1
  have wf' := Judgment.wfkind lem1 wf
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
    simp at j; split at j <;> try simp at j
    case _ wfk =>
    split at j <;> try simp at j
    split at j <;> try simp at j
    case _ κs ret_κ h1 h2 =>
    cases j; case _ τs j =>
    simp at h2; cases h2; case _ h2 h3 =>
    cases h2; case _ h2 h4 =>
    have e := Term.eq_of_beq h2; cases e; clear h2
    cases j; case _ j e =>
    cases e; rw[<-List.mapM'_eq_mapM] at j; rw[List.foldl_eq_foldr_reverse]
    have lem1 := kinding_split_arrow wf (wf_kind_sound wfk wf) h1
    cases lem1; case _ lem1 lem2 =>
    have lem3 := mapM'_elems_image j

    sorry

  case _ tnf ih =>
  rw[tnf] at e; cases e;
  have ih' := ih h e rfl; simp at ih'

case _ k τ tnf tnfp _ _ _ =>
  split at j;
  · cases j
  case _ h1 => rw[h1] at tnf; cases tnf; simp at j
