import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.Shape

-- set_option maxHeartbeats 500000

theorem invert_eq_kind : Γ ⊢ (A ~[K]~ B) : w -> w = ★ := by
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

theorem lam_typing_unique2 : Γ ⊢ `λ[A]b : (A' -t> B) -> A = A' := by
intros tJ; cases tJ; simp_all;

theorem refl_typing_unique : Γ ⊢ refl! K A : t -> (t = (A ~[K]~ A)) := by
intros tJ; cases tJ; simp_all;

theorem inversion_apply_spine :
  Γ ⊢ t.apply_spine sp : A ->
  ∃ B, SpineType Γ sp B A ∧ Γ ⊢ t : B ∧ (∀ T, Γ ⊢ A : T -> Γ ⊢ B : T)
:= by
intro j; induction sp generalizing Γ t A <;> simp at *
case _ =>
  exists A; apply And.intro;
    apply SpineType.refl;
  apply And.intro; assumption
  intro T h; apply h
case _ hd tl ih =>
  cases hd; case _ v a =>
  cases v <;> simp at *
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    cases h2; case _ C D j1 j2 j3 =>
    have lem := classification_lemma j1; simp at lem;
    cases lem;
    case _ h =>
      have uniq := invert_arr_kind h; cases uniq;
    case _ h =>
      cases h; case _ h =>
      cases h; case _ w h =>
      have uniq := invert_arr_kind h; cases uniq;
      subst j3; apply Exists.intro (C -t> D)
      apply And.intro
      apply SpineType.arrow
      apply j2; assumption; assumption
      apply And.intro; assumption
      intro T h4; replace h3 := h3 T h4
      cases h; case _ q1 q2 =>
      have lem1 := beta_empty a q2; simp at lem1
      have lem2 := type_shape lem1 (kind_shape w rfl)
      have lem5 := uniqueness_of_kinds lem2 lem1 h3
      subst lem5; apply Judgment.arrow q1 q2
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    cases h2; case _ C D j1 j2 j3 =>
    have lem := classification_lemma j1; simp at lem;
    cases lem; case _ h => cases h
    case _ h =>
    cases h; case _ h =>
    cases h; case _ w h =>
    have uniq := invert_all_kind h; cases uniq;
    subst j3; apply Exists.intro (∀[C] D)
    apply And.intro;
    apply SpineType.all j2 h
    assumption; apply And.intro j1
    intro T h4; replace h3 := h3 T h4
    cases h; case _ q1 q2 =>
    have lem1 := beta_kind q2 j2; simp at lem1
    have lem2 := type_shape lem1 (kind_shape w rfl)
    have lem5 := uniqueness_of_kinds lem2 lem1 h3
    subst lem5; apply Judgment.allt q1 q2
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 =>
    cases j2; case _ j2 j3 =>
    cases j2; case _ C j2 j4 =>
    have lem := classification_lemma j4; simp at lem;
    cases lem;
    case _ h =>
      apply Exists.intro (C -k> B)
      apply And.intro;
      apply SpineType.arrowk;
      assumption; assumption
      apply j1; apply And.intro j4
      intro T h4; replace j3 := j3 T h4
      cases h; case _ q1 q2 =>
      have lem := uniqueness_of_super_kind (kind_shape q2 rfl) q2 j3
      subst lem; apply Judgment.allk q1 q2
    case _ h =>
      cases h; case _ h =>
      cases h; case _ w h =>
      have uniq := invert_arrk_kind h; cases h; cases w;

theorem apply_spine_typed :
  Γ ⊢ t : A ->
  SpineType Γ sp A B ->
  Γ ⊢ t.apply_spine sp : B
:= by
intro j1 j2
induction j2 generalizing t <;> simp at *
case _ => assumption
case _ c C D sp' T h1 h2 h3 ih =>
  generalize Cdef : D β[c] = C'
  have lem := Judgment.app j1 h1 (by rw [Cdef])
  rw [<-Cdef] at lem; apply ih lem
case _ c C D sp' T h1 h2 h3 ih =>
  generalize Cdef : D β[c] = C'
  have lem := Judgment.appt j1 h1 (by rw [Cdef])
  rw [<-Cdef] at lem; apply ih lem
case _ c C D sp' T h1 h2 h3 ih =>
  have lem := Judgment.appk j1 h1
  apply ih lem

theorem apply_spine_uniform i asp :
  a.neutral_form = .some (i, asp) ->
  Γ ⊢ a : A ->
  Γ ⊢ b : A ->
  Γ ⊢ a.apply_spine sp : B ->
  Γ ⊢ b.apply_spine sp : B
:= by
intro js j1 j2 j3
replace j3 := inversion_apply_spine j3
cases j3; case _ D j3 =>
cases j3; case _ h1 h2 =>
have lem := uniqueness_modulo_neutral_form js j1 h2.1
subst lem; apply apply_spine_typed j2 h1

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
  ¬ (Γ d@ x).get_type = .some (A ~[K]~ B)
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
  SpineType Γ sp τ' τ ->
  Γ ⊢ τ' : ★ := by
intro τJ sp;
induction sp;
case _ => assumption
case _ => assumption
case _ => assumption
case _ h _ ih =>
  replace ih := ih τJ;
  cases h; case _ bj =>
    have lem1 := kind_shape bj rfl
    have lem2 := type_shape ih (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2

theorem spine_type_is_not_kind :
  SpineType Γ sp A T ->
  Γ ⊢ T : ★ ->
  Γ ⊢ A : .kind ->
  False
:= by
intro h1 h2 h3
have h4 := spine_type_is_type h2 h1
have lem1 := kind_shape h3 rfl
have lem2 := type_shape h4 (by constructor)
exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2

theorem valid_ctor_not_equality :
  ¬ (ValidCtorType Γ (A ~[K]~ B))
:= by
intro h
generalize Tdef : (A ~[K]~ B) = T at *
induction h generalizing A B
case _ j =>
  unfold ValidHeadVariable at j; subst Tdef
  simp at *
case _ j ih => injection Tdef
case _ => injection Tdef

theorem spine_type_is_not_valid_ctor :
  T = (C ~[K]~ D) ->
  SpineType Γ sp A T ->
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
  ¬ (ValidInstType Γ (A ~[K]~ B))
:= by
intro h
generalize Tdef : (A ~[K]~ B) = T at *
induction h generalizing A B
case _ j =>
  unfold ValidHeadVariable at j; subst Tdef
  simp at *
case _ j ih => injection Tdef
case _ => injection Tdef

theorem spine_type_is_not_valid_insttype :
  T = (C ~[K]~ D) ->
  SpineType Γ sp A T ->
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

theorem term_has_no_arity :
  Γ ⊢ t : A ->
  Γ ⊢ A : ★ ->
  t.arity = 0
:= by
  intro j1 j2
  cases j1 <;> simp [Term.arity]
  all_goals cases j2

theorem spine_less_than_spine_type :
  sp.length < A.arity ->
  B.ground ->
  SpineType Γ sp A B ->
  False
:= by
  intro h1 h2 j; induction j
  case _ T =>
    simp [Term.ground] at *
    cases T <;> try simp at h2
    case _ => simp [Term.arity] at h1
    case _ v t1 t2 =>
      cases v <;> simp at h2
      simp [Term.arity] at h1
    case _ => simp [Term.arity] at h1
  case _ a A B sp T j1 j2 j3 ih =>
    simp [Term.arity] at h1
    cases j2; case _ j2 j4 =>
    apply ih _ h2; rw [Term.arity_beta]
    exact h1; apply term_has_no_arity j1 j2
  case _ a A B sp T j1 j2 j3 ih =>
    simp [Term.arity] at h1
    cases j2; case _ j2 j4 =>
    have lem1 : B.arity ≤ (B β[a]).arity := Term.arity_subst_leq
    have lem2 : sp.length < (B β[a]).arity := by omega
    apply ih lem2 h2
  case _ a A B sp T j1 j2 j3 ih =>
    simp [Term.arity] at h1
    replace h1 : sp.length < B.arity := by omega
    apply ih h1 h2

theorem ctx_get_var_no_spine_eq_type:
  ⊢ Γ ->
  Γ.is_stable_red x ∨ OpenVarVal Γ x sp ->
  (Γ d@ x).get_type = some T ->
  Γ ⊢ (A ~[K]~ B) : ★ ->
  SpineType Γ sp T (A ~[K]~ B) ->
  False
:= by
intro h1 h2 h3 h4 h5
have lem1 := frame_wf_by_index x h1
simp at *; generalize fdef : Γ d@ x = f at *
cases lem1
all_goals (
  unfold Frame.get_type at h3
  unfold Frame.is_stable_red at h2
  simp [OpenVarVal] at *)
any_goals (rw [fdef] at h2; simp [Frame.is_openm] at h2)
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ j1 j2 => subst h3; apply spine_type_is_not_valid_ctor rfl h5 j2
case _ j => subst h3; apply spine_type_is_not_kind h5 h4 j
case _ C j =>
  subst h3; replace h2 := h2 C; simp [Frame.get_type] at h2
  apply spine_less_than_spine_type h2 _ h5; simp [Term.ground]
case _ j1 j2 => subst h3; apply spine_type_is_not_valid_insttype rfl h5 j2

theorem ctx_get_var_spine_type :
  ⊢ Γ ->
  (Γ d@ n).get_type = some τ' ->
  SpineType Γ sp τ' τ ->
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

theorem invert_ctor1 :
  Γ ⊢ .ctor1 v t : A ->
  ∃ B, Γ ⊢ t : B
:= by
intro j; cases v
cases j; case _ j =>
apply Exists.intro _; apply j

theorem invert_ctor2 :
  Γ ⊢ .ctor2 v t1 t2 : A ->
  ∃ B C, Γ ⊢ t1 : B ∧ Γ ⊢ t2 : C
:= by
intro j; cases v
all_goals try solve | (
  case _ =>
    cases j; case _ j1 j2 =>
    apply Exists.intro _
    apply Exists.intro _
    apply And.intro j1 j2
)
case _ =>
  cases j; case _ j1 j2 j3 =>
  have lem := classification_lemma j1; simp at lem
  cases lem; case inr h =>
    cases h; case _ h =>
    cases h; case _ h1 h2 =>
    cases h2; cases h1
  case inl h =>
  cases h; case _ j4 j5 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j4 j3
case _ =>
  cases j; case _ j1 j2 j3 j4 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j1 j4
case _ =>
  cases j; case _ j1 j2 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j2 j1
case _ =>
  cases j; case _ j1 j2 j3 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j1 j2
case _ =>
  cases j; case _ j1 j2 j3 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j1 j2

theorem invert_bind2 :
  Γ ⊢ .bind2 v t1 t2 : A ->
  ∃ B C, Γ ⊢ t1 : B ∧ (bind2_frame t1 v :: Γ) ⊢ t2 : C
:= by
intro j; cases v
all_goals try solve | (
  case _ =>
    cases j; case _ j1 j2 =>
    apply Exists.intro _
    apply Exists.intro _
    apply And.intro j1 j2
)
case _ =>
  cases j; case _ j1 j2 j3 =>
  cases j2; case _ j2 j4 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j1 j3
case _ =>
  cases j; case _ j1 j2 j3 =>
  cases j2; case _ j2 j4 =>
  apply Exists.intro _
  apply Exists.intro _
  apply And.intro j1 j3
