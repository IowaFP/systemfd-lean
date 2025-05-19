import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Inversion
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Substitution
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.Classification

theorem preservation_inst_lemma :
  Γ ⊢ t : A ->
  t.neutral_form = .some (x, sp) ->
  Γ.is_openm x ->
  w ∈ get_instances Γ x ->
  Γ ⊢ w.apply_spine sp : A
:= by
intro j1 j2 j3 j4
replace j2 := Term.neutral_form_law (Eq.symm j2); subst j2
simp at j3; replace j3 := Frame.is_openm_destruct j3
cases j3; case _ T j3 =>
  have lem := ctx_get_instance_well_typed (judgment_ctx_wf j1) j3 j4
  apply apply_spine_uniform x [] (by simp) lem.1 lem.2 j1

theorem preservation_letterm_lemma :
  Γ ⊢ a : A ->
  a.neutral_form = some (x, sp) ->
  Frame.term T t = Γ d@ x ->
  Γ ⊢ t.apply_spine sp : A
:= by
intro j1 j2 j3
replace j2 := Term.neutral_form_law (Eq.symm j2); subst j2
replace j3 := ctx_get_term_well_typed (judgment_ctx_wf j1) (Eq.symm j3)
apply apply_spine_uniform x [] (by simp) j3.1 j3.2 j1

theorem preservation_prefix_match_lemma :
  a.neutral_form = some (x, sp) ->
  Γ ⊢ a : A ->
  Γ ⊢ a.apply_spine ξ : R ->
  Γ ⊢ t : B ->
  StableTypeMatch Γ A R ->
  PrefixTypeMatch Γ A B T ->
  Γ ⊢ t.apply_spine ξ : T
:= by
intro js j1 j2 j3 j4 j5
induction ξ generalizing Γ A R B T a t x sp <;> simp at *
case _ =>
  have lem := uniqueness_modulo_neutral_form js j1 j2; subst lem
  replace j4 := stable_type_match_refl_inversion j4
  have lem := prefix_type_match_forced_refl j4 j5; subst lem
  apply j3
case _ hd tl ih =>
  cases j4
  case _ h =>
    cases hd; case _ v hd =>
    cases v <;> simp at *
    case _ =>
      replace j2 := inversion_apply_spine j2
      cases j2; case _ W j2 =>
      cases j2; case _ j2 =>
      cases j2; case _ j2 _ =>
      cases j2; case _ C D q1 q2 q3 =>
        have lem := uniqueness_modulo_neutral_form js j1 q1
        subst lem; unfold ValidHeadVariable at h
        simp at h
    case _ =>
      replace j2 := inversion_apply_spine j2
      cases j2; case _ W j2 =>
      cases j2; case _ j2 =>
      cases j2; case _ j2 _ =>
      cases j2; case _ C D q1 q2 q3 =>
        have lem := uniqueness_modulo_neutral_form js j1 q1
        subst lem; unfold ValidHeadVariable at h
        simp at h
    case _ =>
      replace j2 := inversion_apply_spine j2
      cases j2; case _ W j2 =>
      cases j2; case _ j2 =>
      cases j2; case _ j2 _ =>
      cases j2; case _ A q1 q2 =>
        have lem := uniqueness_modulo_neutral_form js j1 q2
        subst lem; unfold ValidHeadVariable at h
        simp at h
  case _ U V _ h1 =>
    cases j5
    case _ h2 =>
      exfalso; apply no_valid_head_variable_with_arrow h2
    case _ V' h2 =>
      cases hd; case _ v q =>
      cases v <;> simp at *
      case _ =>
        have lem0 := inversion_apply_spine j2
        cases lem0; case _ W lem0 =>
        cases lem0; case _ lem0 =>
        cases lem0; case _ lem0 _ =>
        cases lem0; case _ q1 q2 q3 =>
          have lem0 := uniqueness_modulo_neutral_form js j1 q1
          injection lem0 with _ e1 e2; subst e1; subst e2
          have lem1 : Γ ⊢ q : V := q2
          have lem2 := Judgment.app j3 lem1 rfl
          have lem3 := Judgment.app j1 lem1 rfl
          replace h1 := stable_type_match_beta q (by unfold Frame.is_stable; simp) h1
          replace h2 := prefix_type_match_beta q (by unfold Frame.is_stable; simp) h2
          simp at h1; simp at h2
          apply @ih x (sp ++ [(.term, q)]) _ _ _ _ _ _ _ _ lem3 j2 lem2 h1 h2
          simp; rw [Option.bind_eq_some]; simp; apply js
      case _ =>
        replace j2 := inversion_apply_spine j2
        cases j2; case _ W j2 =>
        cases j2; case _ j2 =>
        cases j2; case _ j2 _ =>
        cases j2; case _ C D q1 q2 q3 =>
        have lem := uniqueness_modulo_neutral_form js j1 q1
        injection lem with e; injection e
      case _ =>
        replace j2 := inversion_apply_spine j2
        cases j2; case _ W j2 =>
        cases j2; case _ j2 =>
        cases j2; case _ j2 _ =>
        cases j2; case _ C q1 q2 =>
        have lem := uniqueness_modulo_neutral_form js j1 q2
        injection lem
  case _ U V _ h1 =>
    cases j5
    case _ h2 =>
      exfalso; apply no_valid_head_variable_with_all h2
    case _ V' h2 =>
      cases hd; case _ v q =>
      cases v <;> simp at *
      case _ =>
        replace j2 := inversion_apply_spine j2
        cases j2; case _ W j2 =>
        cases j2; case _ j2 =>
        cases j2; case _ j2 _ =>
        cases j2; case _ C D q1 q2 q3 =>
        have lem := uniqueness_modulo_neutral_form js j1 q1
        injection lem with e; injection e
      case _ =>
        have lem0 := inversion_apply_spine j2
        cases lem0; case _ W lem0 =>
        cases lem0; case _ lem0 =>
        cases lem0; case _ lem0 _ =>
        cases lem0; case _ q1 q2 q3 =>
        have lem0 := uniqueness_modulo_neutral_form js j1 q1
        injection lem0 with _ e1 e2; subst e1; subst e2
        have lem1 : Γ ⊢ q : U := q2
        have lem2 := Judgment.appt j3 lem1 rfl
        have lem3 := Judgment.appt j1 lem1 rfl
        replace h1 := stable_type_match_beta q (by unfold Frame.is_stable; simp) h1
        replace h2 := prefix_type_match_beta q (by unfold Frame.is_stable; simp) h2
        simp at h1; simp at h2
        apply @ih x (sp ++ [(.type, q)]) _ _ _ _ _ _ _ _ lem3 j2 lem2 h1 h2
        simp; rw [Option.bind_eq_some]; simp; apply js
      case _ =>
        replace j2 := inversion_apply_spine j2
        cases j2; case _ W j2 =>
        cases j2; case _ j2 =>
        cases j2; case _ j2 _ =>
        cases j2; case _ C q1 q2 =>
        have lem := uniqueness_modulo_neutral_form js j1 q2
        injection lem

theorem preservation_prefix_match {p s t : Term} :
  Γ ⊢ p : A ->
  Γ ⊢ s : R ->
  Γ ⊢ t : B ->
  StableTypeMatch Γ A R ->
  PrefixTypeMatch Γ A B T ->
  some ξ = prefix_equal sp sp' ->
  some (x, sp) = p.neutral_form ->
  some (x, sp') = s.neutral_form ->
  Γ ⊢ t.apply_spine ξ : T
:= by
intro j1 j2 j3 j4 j5 j6 j7 j8
replace j6 := prefix_equal_law j6; subst j6
have h7 := Term.neutral_form_law j7; subst h7
replace j8 := Term.neutral_form_law j8; subst j8
rw [Term.apply_spine_compose] at j2
apply preservation_prefix_match_lemma (Eq.symm j7) j1 j2 j3 j4 j5

theorem type_choice_list :
  t = List.foldl (·⊕·) a tl ->
  Γ ⊢ A : ★ ->
  Γ ⊢ a : A ->
  (∀ x, x ∈ tl -> Γ ⊢ x : A) ->
  Γ ⊢ t : A
:= by
intro h1 h2 h3 h4
induction tl generalizing t Γ A a <;> simp at *
subst h1; assumption
case _ hd tl ih =>
  apply @ih t (a ⊕ hd) Γ A h1 h2 _ h4.2
  apply Judgment.choice _ h2 h3 h4.1
  constructor; apply judgment_ctx_wf h2

@[simp]
abbrev PreservationLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, A) => ∀ {t'}, Red Γ t t' -> Γ ⊢ t' : A
| .wf => λ () => True

theorem preservation_lemma : Judgment v Γ ix -> PreservationLemmaType Γ v ix := by
intro j
induction j <;> simp at *
all_goals (intro t' r)
any_goals (solve | cases r <;> simp at *)
case letterm j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  cases r
  case _ =>
    have lem := beta_term j3 j2
    simp at lem; apply lem
  case _ h _ => cases h
  case _ h => cases h
case var Γ x T j1 j2 _ =>
  cases r
  case _ i sp tl tl' h1 h2 h3 h4 h5 =>
    simp at h4; cases h4; case _ e1 e2 =>
      subst e1; subst e2
      simp at h1; subst h1
      have lem1 := frame_wf_by_index i j1
      have lem2 := frame_wf_openm_implies_type T lem1 j2 h2
      have lem3 : Γ ⊢ `0 : T := by
        apply Judgment.empty _ lem2
        constructor; apply judgment_ctx_wf lem2
      apply type_choice_list h5 lem2 lem3
      intro x h; subst h3
      replace h := get_instances_sound h
      cases h; case _ y h =>
      have lem := frame_wf_by_index y j1
      rw [h] at lem
      cases lem; case _ T' q1 q2 =>
      rw [<-q1] at j2
      unfold Frame.get_type at j2; simp at j2
      subst j2; apply q2
  case _ T' i sp t h1 h2 =>
    simp at h2; cases h2; case _ e1 e2 =>
      subst e1; subst e2; simp
      have lem := frame_wf_by_index i j1
      rw [<-h1] at lem
      cases lem; case _ q1 q2 =>
      rw [<-h1] at j2; unfold Frame.get_type at j2
      simp at j2; subst j2; apply q2
case appk Γ f A B a j1 j2 ih1 ih2 =>
  cases r
  case _ x sp tl tl' h1 h2 h3 h4 h5 =>
    have lem := frame_wf_by_index x (judgment_ctx_wf j1)
    have lem2 := Frame.is_openm_destruct h2
    cases lem2; case _ T lem2 =>
    rw [lem2] at lem; cases lem; case _ q1 =>
    have lem3 := Term.neutral_form_law h4
    have j3 := Judgment.appk j1 j2
    rw [<-lem3] at j3
    have lem4 := inversion_apply_spine j3
    cases lem4; case _ T' lem4 =>
    cases lem4.2.1; case _ h1 h2 =>
    rw [lem2] at h2; unfold Frame.get_type at h2
    simp at h2; subst h2
    have lem5 := classification_lemma j1; simp at lem5
    cases lem5; case inr lem5 =>
      cases lem5; case _ K lem5 =>
      cases lem5.2; cases lem5.1
    case _ lem5 =>
    cases lem5; case _ w1 w2 =>
      have lem6 := lem4.2.2 _ w2
      have lem7 := kind_shape lem6 rfl
      have lem8 := type_shape q1 (by constructor)
      exfalso; apply Term.is_kind_disjoint_is_type lem7 lem8
  case _ T x sp t h1 h2 =>
    apply preservation_letterm_lemma _ (Eq.symm h2) h1
    apply Judgment.appk j1 j2
  case _ h _ => cases h
  case _ h _ => cases h
  case _ h => cases h
  case _ h => cases h
  case _ h _ => cases h
  case _ h _ => cases h
case ite j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
  cases r
  case _ h1 h2 h3 h4 =>
    apply preservation_prefix_match j1 j2 j4 j7 j8 h1 h3 h4
  case _ => apply j10
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.ite j1 (ih2 r) j3 j4 j5 j6 j7 j8 j9 j10
  case _ =>
    apply Judgment.empty _ j9
    constructor; apply judgment_ctx_wf j1
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    apply Judgment.choice _ j9
    apply Judgment.ite j1 q3 j3 j4 j5 j6 j7 j8 j9 j10
    apply Judgment.ite j1 q4 j3 j4 j5 j6 j7 j8 j9 j10
    constructor; apply judgment_ctx_wf j1
case guard j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
  cases r
  case _ h1 h2 h3 =>
    apply preservation_prefix_match j1 j2 j4 j7 j8 h1 h2 h3
  case _ =>
    apply Judgment.empty _ j9
    constructor; apply judgment_ctx_wf j1
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.guard j1 (ih2 r) j3 j4 j5 j6 j7 j8 j9
  case _ =>
    apply Judgment.empty _ j9
    constructor; apply judgment_ctx_wf j1
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    apply Judgment.choice _ j9
    apply Judgment.guard j1 q3 j3 j4 j5 j6 j7 j8 j9
    apply Judgment.guard j1 q4 j3 j4 j5 j6 j7 j8 j9
    constructor; apply judgment_ctx_wf j1
case app Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  have lem : Γ ⊢ (A -t> B) : ★ := by
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; apply lem.2
  cases lem; case _ lem1 lem2 =>
  have lem3 : Γ ⊢ B' : ★ := by
    have lem := beta_empty a lem2
    subst j3; simp at lem; apply lem
  have lem4 : Γ ⊢ `0 : B' := by
    apply Judgment.empty _ lem3
    constructor; apply judgment_ctx_wf lem1
  cases r
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    have lem := beta_type q3 j2
    subst j3; apply lem
  case _ x sp tl tl' h1 h2 h3 h4 h5 =>
    apply type_choice_list h5 lem3 lem4; clear h5
    intro y h6; subst h3; subst h1; simp at h6
    cases h6; case _ w h3 =>
    cases h3; case _ h3 h5 =>
    replace h5 := Eq.symm h5; subst h5
    have lem5 := get_instances_sound h3
    cases lem5; case _ j lem5 =>
    simp at h4; replace h4 := Option.bind_eq_some.1 (Eq.symm h4)
    cases h4; case _ q h4 =>
    cases q; case _ z sp' =>
    simp at h4; cases h4; case _ h4 h5 =>
    cases h5; case _ h5 h6 =>
    subst h5; replace h6 := Eq.symm h6; subst h6
    rw [Term.apply_spine_peel_term]
    apply Judgment.app _ j2 j3
    apply preservation_inst_lemma j1 h4 h2 h3
  case _ T x sp t h1 h2 =>
    apply preservation_letterm_lemma _ (Eq.symm h2) h1
    apply Judgment.app j1 j2 j3
  case _ r => apply Judgment.app (ih1 r) j2 j3
  case _ h _ => cases h
  case _ =>
    cases j1; case _ j1 =>
    cases j1; case _ q1 q2 q3 =>
    have lem := beta_empty a q2
    subst j3; simp at lem
    apply Judgment.empty _ lem
    constructor; apply judgment_ctx_wf lem
  case _ h => cases h
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases q1; case _ q1 q4 q5 =>
    have lem := beta_empty a q4; simp at lem
    subst j3; apply Judgment.choice _ lem
    apply Judgment.app q2 j2 rfl
    apply Judgment.app q3 j2 rfl
    constructor; apply judgment_ctx_wf q1
  case _ h _ => cases h
case appt Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  have lem : Γ ⊢ ∀[A] B : ★ := by
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; apply lem.2
  cases lem; case _ lem1 lem2 =>
  have lem3 : Γ ⊢ B' : ★ := by
    have lem := beta_kind lem2 j2
    subst j3; simp at lem; apply lem
  have lem4 : Γ ⊢ `0 : B' := by
    apply Judgment.empty _ lem3
    constructor; apply judgment_ctx_wf lem1
  cases r
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    have lem := beta_kind q3 j2
    subst j3; apply lem
  case _ x sp tl tl' h1 h2 h3 h4 h5 =>
    apply type_choice_list h5 lem3 lem4; clear h5
    intro y h6; subst h3; subst h1; simp at h6
    cases h6; case _ w h3 =>
    cases h3; case _ h3 h5 =>
    replace h5 := Eq.symm h5; subst h5
    have lem5 := get_instances_sound h3
    cases lem5; case _ j lem5 =>
    simp at h4; replace h4 := Option.bind_eq_some.1 (Eq.symm h4)
    cases h4; case _ q h4 =>
    cases q; case _ z sp' =>
    simp at h4; cases h4; case _ h4 h5 =>
    cases h5; case _ h5 h6 =>
    subst h5; replace h6 := Eq.symm h6; subst h6
    rw [Term.apply_spine_peel_type]
    apply Judgment.appt _ j2 j3
    apply preservation_inst_lemma j1 h4 h2 h3
  case _ T x sp t h1 h2 =>
    apply preservation_letterm_lemma _ (Eq.symm h2) h1
    apply Judgment.appt j1 j2 j3
  case _ r => apply Judgment.appt (ih1 r) j2 j3
  case _ h _ => cases h
  case _ =>
    cases j1; case _ j1 =>
    cases j1; case _ q1 q2 q3 =>
    have lem := beta_kind q2 j2
    subst j3; simp at lem
    apply Judgment.empty _ lem
    constructor; apply judgment_ctx_wf q1
  case _ h => cases h
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases q1; case _ q1 q4 q5 =>
    have lem := beta_kind q4 j2; simp at lem
    subst j3; apply Judgment.choice _ lem3
    apply Judgment.appt q2 j2 rfl
    apply Judgment.appt q3 j2 rfl
    constructor; apply judgment_ctx_wf q2
  case _ h _ => cases h
case cast j1 j2 ih1 ih2 =>
  have lem1 := classification_lemma j2; simp at lem1
  cases lem1; case _ lem1 => cases lem1
  case _ lem1 =>
  cases lem1; case _ K lem1 =>
  cases lem1.2; case _ q1 q2 q3 =>
  cases r
  case _ => cases j2; apply j1
  case _ h _ => cases h
  case _ h => cases h
  case _ h _ => cases h
  case _ r => apply Judgment.cast j1 (ih2 r)
  case _ h => cases h
  case _ => apply Judgment.empty q1 q3
  case _ h _ => cases h
  case _ =>
    cases j2; case _ w1 w2 w3 w4 =>
    apply Judgment.choice q1 q3
    apply Judgment.cast j1 w3
    apply Judgment.cast j1 w4
case sym j ih =>
  cases r
  case _ =>
    cases j; case _ j1 j2 =>
    apply Judgment.refl j1 j2
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.sym (ih r)
  case _ =>
    cases j; case _ j1 j2 =>
    cases j2; case _ q1 q2 q3 =>
    apply Judgment.empty j1
    apply Judgment.eq q1 q3 q2
  case _ =>
    cases j; case _ q1 q2 q3 q4 =>
    apply Judgment.choice q1 _
    apply Judgment.sym q3
    apply Judgment.sym q4
    cases q2; case _ w1 w2 w3 =>
    apply Judgment.eq w1 w3 w2
case seq j1 j2 ih1 ih2 =>
  cases r
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2
    apply Judgment.refl q1 q2
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.seq (ih1 r) j2
  case _ r => apply Judgment.seq j1 (ih2 r)
  case _ =>
    cases j1; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j2 <;> simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.empty lem.1
    apply Judgment.eq q2 q3 w3
  case _ =>
    cases j2; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j1 <;> simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.empty q1
    apply Judgment.eq q2 w2 q4
  case _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem := classification_lemma j2 <;> simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.choice q1
    apply Judgment.eq q2 q5 w3
    apply Judgment.seq q3 j2
    apply Judgment.seq q4 j2
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem := classification_lemma j1 <;> simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.choice lem.1
    apply Judgment.eq q2 w2 q6
    apply Judgment.seq j1 q3
    apply Judgment.seq j1 q4
case appc j1 j2 ih1 ih2 =>
  cases r
  case _ =>
    cases j1; case _ q1 q2 =>
    cases q1; case _ q1 q3 =>
    cases j2; case _ w1 w2 =>
    apply Judgment.refl q3
    apply Judgment.appk q2 w2
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.appc (ih1 r) j2
  case _ r => apply Judgment.appc j1 (ih2 r)
  case _ =>
    cases j1; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    cases q2; case _ q2 q5 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.empty q1
    apply Judgment.eq q5
    apply Judgment.appk q3 w2
    apply Judgment.appk q4 w3
  case _ =>
    cases j2; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    cases w1; case _ w1 w4 =>
    apply Judgment.empty q1
    apply Judgment.eq w4
    apply Judgment.appk w2 q3
    apply Judgment.appk w3 q4
  case _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    cases q2; case _ q2 q7 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.choice q1
    apply Judgment.eq q7
    apply Judgment.appk q5 w2
    apply Judgment.appk q6 w3
    apply Judgment.appc q3 j2
    apply Judgment.appc q4 j2
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
      have lem := classification_lemma j1; simp at lem
      cases lem; case _ lem => cases lem
      case _ lem =>
      cases lem; case _ K lem =>
      cases lem.2; case _ w1 w2 w3 =>
      cases w1; case _ w1 w4 =>
        apply Judgment.choice q1
        apply Judgment.eq w4
        apply Judgment.appk w2 q5
        apply Judgment.appk w3 q6
        apply Judgment.appc j1 q3
        apply Judgment.appc j1 q4
case arrowc j1 j2 ih1 ih2 =>
  cases r
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ w1 w2 =>
    apply Judgment.refl q1
    apply Judgment.arrow q2 w2
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.arrowc (ih1 r) j2
  case _ r => apply Judgment.arrowc j1 (ih2 r)
  case _ =>
    cases j1; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.empty q1
    apply Judgment.eq q1
    apply Judgment.arrow q3 w2
    apply Judgment.arrow q4 w3
  case _ =>
    cases j2; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.empty w1
    apply Judgment.eq w1
    apply Judgment.arrow w2 q3
    apply Judgment.arrow w3 q4
  case _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.choice q2
    apply Judgment.eq q2
    apply Judgment.arrow q5 w2
    apply Judgment.arrow q6 w3
    apply Judgment.arrowc q3 j2
    apply Judgment.arrowc q4 j2
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    apply Judgment.choice w1
    apply Judgment.eq w1
    apply Judgment.arrow w2 q5
    apply Judgment.arrow w3 q6
    apply Judgment.arrowc j1 q3
    apply Judgment.arrowc j1 q4
case fst j1 j2 j3 ih1 ih2 ih3 =>
  cases r
  case _ =>
    cases j3; case _ q1 q2 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case inr lem =>
      cases lem; case _ K lem =>
      cases lem.2; cases lem.1
    case _ lem =>
      apply Judgment.refl lem j1
  case _ h _ => cases h
  case _ h => cases h
  case _ h _ => cases h
  case _ r => apply Judgment.fst j1 j2 (ih3 r)
  case _ h => cases h
  case _ =>
    cases j3; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    cases q3; case _ K3 q3 q5 =>
    cases q4; case _ K3 q4 q6 =>
    have lem1 := classification_lemma j1; simp at lem1
    cases lem1; case inr lem =>
      cases lem; case _ K lem =>
      cases lem.2; cases lem.1
    case _ lem =>
      have lem3 := type_shape j2 (kind_shape lem rfl)
      have lem5 := uniqueness_of_kinds lem3 j2 q6
      injection lem5 with _ e; subst e
      apply Judgment.empty q1
      apply Judgment.eq lem j1 q6
  case _ h _ => cases h
  case _ =>
    cases j3; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem1 := classification_lemma j1; simp at lem1
    cases lem1; case inr lem =>
      cases lem; case _ K lem =>
      cases lem.2; cases lem.1
    case _ lem1 =>
      apply Judgment.choice q1
      apply Judgment.eq lem1 j1 j2
      apply Judgment.fst j1 j2 q3
      apply Judgment.fst j1 j2 q4
case snd j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  cases r
  case _ =>
    cases j4; case _ q1 q2 =>
    apply Judgment.refl j1 j2
  case _ h _ => cases h
  case _ h => cases h
  case _ h _ => cases h
  case _ r => apply Judgment.snd j1 j2 j3 (ih4 r)
  case _ h => cases h
  case _ =>
    apply Judgment.empty _
    apply Judgment.eq j1 j2 j3
    constructor; apply judgment_ctx_wf j1
  case _ h _ => cases h
  case _ =>
    cases j4; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    apply Judgment.choice q1
    apply Judgment.eq j1 j2 j3
    apply Judgment.snd j1 j2 j3 q3
    apply Judgment.snd j1 j2 j3 q4
case allc j1 j2 ih1 ih2 =>
  cases r
  case _ =>
    cases j2; case _ q1 q2 =>
    apply Judgment.refl _
    apply Judgment.allt j1 q2
    constructor; apply judgment_ctx_wf j1
  case _ h _ => cases h
  case _ h => cases h
  case _ h _ => cases h
  case _ r => apply Judgment.allc j1 (ih2 r)
  case _ h => cases h
  case _ =>
    cases j2; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    apply Judgment.empty _
    apply Judgment.eq _
    apply Judgment.allt j1 q3
    apply Judgment.allt j1 q4
    constructor; apply judgment_ctx_wf j1
    constructor; apply judgment_ctx_wf j1
  case _ h => cases h
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    apply Judgment.choice _
    apply Judgment.eq _
    apply Judgment.allt j1 q5
    apply Judgment.allt j1 q6
    constructor; apply judgment_ctx_wf j1
    apply Judgment.allc j1 q3
    apply Judgment.allc j1 q4
    constructor; apply judgment_ctx_wf j1
case apptc j1 j2 j3 j4 ih1 ih2 =>
  cases r
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ q3 q4 =>
    cases q2; case _ q2 q5 =>
    subst j3; subst j4
    apply Judgment.refl q3
    apply beta_kind q5 q4
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.apptc (ih1 r) j2 j3 j4
  case _ r => apply Judgment.apptc j1 (ih2 r) j3 j4
  case _ =>
    cases j1; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    cases q3; case _ w1 w2 =>
    cases q4; case _ w3 w4 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ h1 h2 h3 =>
    apply Judgment.empty q1
    apply Judgment.eq q1; subst j3
    apply beta_kind w2 h2; subst j4
    apply beta_kind w4 h3
  case _ =>
    cases j2; case _ q1 q2 =>
    cases q2; case _ q2 q3 q4 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    cases w2; case _ h1 h2 =>
    cases w3; case _ h3 h4 =>
    apply Judgment.empty q1
    apply Judgment.eq q1; subst j3
    apply beta_kind h2 q3; subst j4
    apply beta_kind h4 q4
  case _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    cases q5; case _ w1 w2 =>
    cases q6; case _ w3 w4 =>
    have lem := classification_lemma j2; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ h1 h2 h3 =>
    apply Judgment.choice q1
    apply Judgment.eq q1; subst j3
    apply beta_kind w2 h2; subst j4
    apply beta_kind w4 h3
    apply Judgment.apptc q3 j2 j3 j4
    apply Judgment.apptc q4 j2 j3 j4
  case _ =>
    cases j2; case _ q1 q2 q3 q4 =>
    cases q2; case _ q2 q5 q6 =>
    have lem := classification_lemma j1; simp at lem
    cases lem; case _ lem => cases lem
    case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ w1 w2 w3 =>
    cases w2; case _ h1 h2 =>
    cases w3; case _ h3 h4 =>
    apply Judgment.choice q1
    apply Judgment.eq q1; subst j3
    apply beta_kind h2 q5; subst j4
    apply beta_kind h4 q6
    apply Judgment.apptc j1 q3 j3 j4
    apply Judgment.apptc j1 q4 j3 j4
case choice j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  cases r
  case _ => assumption
  case _ => assumption
  case _ h _ => cases h
  case _ h => cases h
  case _ r => apply Judgment.choice j1 j2 (ih3 r) j4
  case _ r => apply Judgment.choice j1 j2 j3 (ih4 r)
  case _ => apply Judgment.empty j1 j2
  case _ => apply Judgment.empty j1 j2
  case _ h => exfalso; apply h rfl
  case _ h => exfalso; apply h rfl

theorem preservation :
  Γ ⊢ t : A ->
  RedStar Γ t t' ->
  Γ ⊢ t' : A
:= by
intro j1 r
induction r
case _ => apply j1
case _ r ih => apply preservation_lemma ih r
