import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Classification

set_option maxHeartbeats 500000

theorem invert_eq_kind : Γ ⊢ (A ~ B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_arr_kind : Γ ⊢ (A -t> B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_arrk_kind : Γ ⊢ (A -k> B) : w -> w = .kind := by
intros eqJ; cases eqJ; simp_all;

theorem invert_all_kind : (Γ ⊢ ∀[ A ] B : w) -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem lamt_typing_unique : Γ ⊢ Λ[A]b : t -> ∃ B', t = ∀[A] B' := by
intros tJ; cases tJ; simp_all;

theorem lam_typing_unique : Γ ⊢ `λ[A]b : t -> ∃ B', (t = (A -t> B')) := by
intros tJ; cases tJ; simp_all;

theorem refl_typing_unique : Γ ⊢ refl! A : t -> (t = (A ~ A)) := by
intros tJ; cases tJ; simp_all;


theorem inversion_apply_spine :
  Γ ⊢ t.apply_spine sp : A ->
  ∃ B, SpineType Γ B A ∧ Γ ⊢ t : B
:= by
intro j; induction sp generalizing Γ t A <;> simp at *
case _ =>
  exists A; apply And.intro;
    apply SpineType.refl;
  assumption
case _ hd tl ih =>
  cases hd; case _ v a =>
  cases v <;> simp at *
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ h1 h2 =>
    cases h2; case _ C D j1 j2 j3 =>
      have lem := classification_lemma j1; simp at lem;
      cases lem;
      case _ h =>
        have uniq := invert_arr_kind h; cases uniq;
      case _ h =>
      cases h; case _ h =>
        cases h; case _ h =>
        have uniq := invert_arr_kind h; cases uniq;
        subst j3; apply Exists.intro (C -t> D)
        apply And.intro;
          apply SpineType.arrow;
          apply j2;
          assumption;
          assumption;
        assumption
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ h1 h2 =>
    cases h2; case _ C D j1 j2 j3 =>
      have lem := classification_lemma j1; simp at lem;
      cases lem;
      case _ h =>
        have uniq := invert_all_kind h; cases h
      case _ h =>
        cases h; case _ h =>
        cases h; case _ h =>
        have uniq := invert_all_kind h; cases uniq;
        subst j3; apply Exists.intro (∀[C] D)
        apply And.intro;
          apply SpineType.all;
          apply j2;
          assumption;
          apply h1;
        apply j1

  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 =>
    cases j2; case _ C j2 j3 =>
      have lem := classification_lemma j3; simp at lem;
      cases lem;
      case _ h =>
        apply Exists.intro (C -k> B)
        apply And.intro;
        apply SpineType.arrowk;
        assumption
        apply j1;
        assumption
      case _ h =>
        cases h; case _ h =>
        cases h; case _ w h =>
        have uniq := invert_arrk_kind h; cases h; cases w;

theorem apply_spine_uniform :
  Γ ⊢ a : A ->
  Γ ⊢ b : A ->
  Γ ⊢ a.apply_spine sp : B ->
  Γ ⊢ b.apply_spine sp : B
:= by
intro j1 j2 j3
induction sp generalizing Γ a b A B <;> simp at *
case _ =>
  have lem := uniqueness_of_types j1 j3; subst lem
  apply j2
case _ hd tl ih =>
  cases hd; case _ v t =>
  cases v <;> simp at *
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ lem =>
    cases lem; case _ U V q1 q2 q3 =>
      have lem1 := uniqueness_of_types j1 q1; subst lem1
      have lem2 : Γ ⊢ (a `@ t) : (V β[t]) := by
        constructor; apply q1; apply q2; simp
      have lem3 : Γ ⊢ (b `@ t) : (V β[t]) := by
        constructor; apply j2; apply q2; simp
      apply ih lem2 lem3 j3
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ lem =>
    cases lem; case _ U V q1 q2 q3 =>
      have lem1 := uniqueness_of_types j1 q1; subst lem1
      have lem2 : Γ ⊢ (a `@t t) : (V β[t]) := by
        constructor; apply q1; apply q2; simp
      have lem3 : Γ ⊢ (b `@t t) : (V β[t]) := by
        constructor; apply j2; apply q2; simp
      apply ih lem2 lem3 j3
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ lem =>
    cases lem; case _ U q1 q2 =>
      have lem1 := uniqueness_of_types j1 q2; subst lem1
      have lem2 : Γ ⊢ (a `@k t) : D := by
        constructor; apply q2; apply q1
      have lem3 : Γ ⊢ (b `@k t) : D := by
        constructor; apply j2; apply q1
      apply ih lem2 lem3 j3

theorem ctx_get_term_well_typed :
  ⊢ Γ ->
  Γ d@ x = .term T t ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by
intro h1 h2
have lem1 := frame_wf_by_index x h1
have lem2 := frame_wf_implies_typed_var T lem1 (by rw [h2]; unfold Frame.get_type; simp)
rw [h2] at lem1; cases lem1
case _ j1 j2 => apply And.intro lem2 j2

theorem ctx_get_instance_well_typed :
  ⊢ Γ ->
  Γ d@ x = .openm T ->
  t ∈ get_instances Γ x ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by
intro h1 h2 h3
have lem1 := frame_wf_by_index x h1
have lem2 := frame_wf_implies_typed_var T lem1 (by rw [h2]; unfold Frame.get_type; simp)
have lem3 := get_instances_sound h3
cases lem3; case _ i lem3 =>
  have lem4 := frame_wf_by_index i h1
  rw [lem3] at lem4; cases lem4
  case _ A q1 q2 =>
    rw [<-q1] at h2; injection h2 with e
    subst e
    apply And.intro lem2 q2

theorem ctx_get_opent_kind : ⊢ Γ -> Γ d@ x = .opent t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_datatype_kind : ⊢ Γ -> Γ d@ x = .datatype t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_var_type : ⊢ Γ -> Γ d@ x = .kind t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_var_type_star : ⊢ Γ -> Γ d@ x = .type t -> Γ ⊢ t : ★ := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_var_ctor : ⊢ Γ -> Γ d@ x = .ctor t -> Γ ⊢ t : ★ := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ => assumption

theorem ctx_get_var_insttype : ⊢ Γ -> Γ d@ x = .insttype t -> Γ ⊢ t : ★ := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ => assumption

theorem ctx_get_var_openm : ⊢ Γ -> Γ d@ x = .openm t -> Γ ⊢ t : ★ := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ => assumption

theorem ctx_get_var_term : ⊢ Γ -> Γ d@ x = .term t t' -> Γ ⊢ t : ★ := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ => assumption


theorem ctx_get_var_no_eq_type :
  ⊢ Γ ->
  Γ.is_stable_red x ->
  ¬ (Γ d@ x).get_type = .some (A ~ B)
:= by
intro h1 h2 h3
have lem1 := frame_wf_by_index x h1
simp at *; generalize fdef : Γ d@ x = f at *
cases lem1
all_goals (
  unfold Frame.get_type at h3
  unfold Frame.is_stable_red at h2; simp at *)
case _ j => subst h3; cases j
case _ j => subst h3; cases j
case _ j1 j2 =>
  subst h3; cases j2
  case _ j2 =>
    unfold ValidHeadVariable at j2; simp at j2
case _ j => subst h3; cases j
case _ j1 j2 =>
  subst h3; cases j2
  case _ j2 =>
    unfold ValidHeadVariable at j2; simp at j2


theorem spine_type_is_type :
  Γ ⊢ τ : ★ ->
  SpineType Γ τ' τ ->
  Γ ⊢ τ' : ★ := by
intro τJ sp;
induction sp;
case _ => assumption
case _ => assumption
case _ => assumption
case _ h _ ih =>
  replace ih := ih τJ;
  cases h; case _ bj => have uniq := uniqueness_of_types ih bj; cases uniq

theorem spine_type_is_not_kind :
  SpineType Γ A T ->
  Γ ⊢ T : ★ ->
  Γ ⊢ A : .kind ->
  False
:= by
intro h1 h2 h3
have h4 := spine_type_is_type h2 h1;
have uniq := uniqueness_of_types h3 h4; cases uniq

theorem valid_ctor_not_equality :
  ¬ (ValidCtorType Γ (A ~ B))
:= by
intro h
generalize Tdef : (A ~ B) = T at *
induction h generalizing A B
case _ j =>
  unfold ValidHeadVariable at j; subst Tdef
  simp at *
case _ j ih => injection Tdef
case _ => injection Tdef

theorem spine_type_is_not_valid_ctor :
  T = (C ~ D) ->
  SpineType Γ A T ->
  ValidCtorType Γ A ->
  False
:= by
intro e h1 h2
induction h1 generalizing C D
case _ =>
  subst e; apply valid_ctor_not_equality h2
case _ j2 ih =>
  cases h2
  case _ h =>
    unfold ValidHeadVariable at h; simp at *
  case _ h =>
    apply @ih C D e; apply valid_ctor_subst _ _ h
    case _ =>
      intro n y h1
      cases n <;> simp at *
      case _ n => subst h1; rw [Frame.apply_compose]; simp
    case _ =>
      intro n h1
      cases n <;> simp at *
      case _ =>
        unfold Frame.apply at h1; simp at h1
        unfold Frame.is_stable at h1; simp at h1
case _ Γ a A B T j1 j2 ih =>
  cases h2
  case _ h =>
    unfold ValidHeadVariable at h; simp at *
  case _ h =>
    apply @ih C D e; apply valid_ctor_subst _ _ h
    case _ =>
      intro n y h1
      cases n <;> simp at *
      case _ n => subst h1; rw [Frame.apply_compose]; simp
    case _ =>
      intro n h1
      cases n <;> simp at *
      case _ =>
        unfold Frame.apply at h1; simp at h1
        unfold Frame.is_stable at h1; simp at h1
case _ B T A j ih =>
  cases h2; case _ h =>
    unfold ValidHeadVariable at h; simp at *

theorem valid_insttype_not_equality :
  ¬ (ValidInstType Γ (A ~ B))
:= by
intro h
generalize Tdef : (A ~ B) = T at *
induction h generalizing A B
case _ j =>
  unfold ValidHeadVariable at j; subst Tdef
  simp at *
case _ j ih => injection Tdef
case _ => injection Tdef

theorem spine_type_is_not_valid_insttype :
  T = (C ~ D) ->
  SpineType Γ A T ->
  ValidInstType Γ A ->
  False
:= by
intro e h1 h2
induction h1 generalizing C D
case _ =>
  subst e; apply valid_insttype_not_equality h2
case _ j2 ih =>
  cases h2
  case _ h =>
    unfold ValidHeadVariable at h; simp at *
  case _ h =>
    apply @ih C D e; apply valid_insttype_subst _ _ h
    case _ =>
      intro n y h1
      cases n <;> simp at *
      case _ n => subst h1; rw [Frame.apply_compose]; simp
    case _ =>
      intro n h1
      cases n <;> simp at *
      case _ =>
        unfold Frame.apply at h1; simp at h1
        unfold Frame.is_stable at h1; simp at h1
case _ Γ a A B T j1 j2 ih =>
  cases h2
  case _ h =>
    unfold ValidHeadVariable at h; simp at *
  case _ h =>
    apply @ih C D e; apply valid_insttype_subst _ _ h
    case _ =>
      intro n y h1
      cases n <;> simp at *
      case _ n => subst h1; rw [Frame.apply_compose]; simp
    case _ =>
      intro n h1
      cases n <;> simp at *
      case _ =>
        unfold Frame.apply at h1; simp at h1
        unfold Frame.is_stable at h1; simp at h1
case _ B T A j ih =>
  cases h2; case _ h =>
    unfold ValidHeadVariable at h; simp at *

theorem ctx_get_var_no_spine_eq_type:
  ⊢ Γ ->
  Γ.is_stable_red x ->
  (Γ d@ x).get_type = some T ->
  Γ ⊢ (A ~ B) : ★ ->
  SpineType Γ T (A ~ B) ->
  False
:= by
intro h1 h2 h3 h4 h5
have lem1 := frame_wf_by_index x h1
simp at *; generalize fdef : Γ d@ x = f at *
cases lem1
all_goals (
  unfold Frame.get_type at h3
  unfold Frame.is_stable_red at h2; simp at *)
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ j1 j2 => subst h3; apply spine_type_is_not_valid_ctor rfl h5 j2
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ j1 j2 => subst h3; apply spine_type_is_not_valid_insttype rfl h5 j2

theorem ctx_get_var_spine_type :
  ⊢ Γ ->
  (Γ d@ n).get_type = some τ' ->
  SpineType Γ τ' τ ->
  Γ ⊢ τ : ★ ->
  Γ ⊢ τ' : ★ := by
intro wf gt spTy τJ;
have spk := spine_type_is_not_kind spTy τJ
unfold Frame.get_type at gt; split at gt;
all_goals (cases gt)
case _ f => have f' := ctx_get_var_type wf f; exfalso; apply spk f'
case _ f => apply ctx_get_var_type_star wf f
case _ f => have f' := ctx_get_datatype_kind wf f; exfalso; apply spk f'
case _ f => apply ctx_get_var_ctor wf f
case _ f => have f' := ctx_get_opent_kind wf f; exfalso; apply spk f'
case _ f => apply ctx_get_var_openm wf f
case _ f => apply ctx_get_var_insttype wf f
case _ f => apply ctx_get_var_term wf f
