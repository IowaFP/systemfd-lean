import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Substitution

theorem preservation_inst_lemma :
  Γ ⊢ t : A ->
  t.neutral_form = .some (x, sp) ->
  Γ.is_openm x' ->
  ixs = instance_indices' Γ 0 x' [] ->
  w ∈ get_instances Γ ixs ->
  Γ ⊢ w.apply_spine sp : A
:= by sorry

theorem preservation_letterm_lemma :
  Γ ⊢ a : A ->
  a.neutral_form = some (x, sp) ->
  Frame.term T t = Γ d@ x ->
  Γ ⊢ t.apply_spine sp : A
:= by sorry

theorem preservation_prefix_match_lemma {p s t : Term} :
  Γ ⊢ p : A ->
  Γ ⊢ s : R ->
  Γ ⊢ t : B ->
  PrefixTypeMatch Γ A B T ->
  some ξ = prefix_equal sp sp' ->
  some (x, sp) = p.neutral_form ->
  some (x, sp') = s.neutral_form ->
  Γ ⊢ t.apply_spine ξ : T
:= by
intro j1 j2 j3 j4 j5 j6 j7
induction j4 generalizing x sp sp' p s ξ t
case _ => sorry
case _ Γ A B V T h ih =>

  sorry
case _ => sorry

@[simp]
abbrev PreservationStepType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, A) => ∀ {ℓ t'}, Red Γ t ℓ -> t' ∈ ℓ -> Γ ⊢ t' : A
| .wf => λ () => True

theorem preservation_step : Judgment v Γ ix -> PreservationStepType Γ v ix := by
intro j
induction j <;> simp at *
all_goals (intro ℓ t' r rin)
any_goals (solve | cases r <;> simp at *)
case _ j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  cases r <;> simp at *; subst rin
  have lem := beta_term j3 j2; simp at lem
  apply lem
case _ wf j _ =>
  cases r <;> try simp at *
  case _ x sp ixs ℓ i1 i2 i3 i4 i5 =>
    cases i5; case _ e1 e2 =>
      subst e1; subst e2
      unfold Frame.is_openm at i1; split at i1 <;> simp at *
      case _ f T h =>
        rw [h] at j; unfold Frame.get_type at j; simp at j
        subst i4; subst j; subst i3
        sorry
  case _ A x sp t h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3; unfold Term.apply_spine at rin
      subst rin; rw [<-h1] at j; unfold Frame.get_type at j; simp at j
      subst j
      sorry
case appk =>
  cases r
  case _ =>
    sorry
  case _ =>
    sorry
case ite j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
  cases r <;> try simp at *
  case _ x sp sp' ξ h1 h2 h3 h4 =>
    subst rin
    apply preservation_prefix_match_lemma j1 j2 j4 j8 h1 h3 h4
  case _ => subst rin; apply j10
  case _ ℓ' r h =>
    subst h; simp at rin
    cases rin; case _ w h =>
    cases h; case _ h1 h2 =>
      subst h2; replace ih2 := ih2 r h1
      apply Judgment.ite j1 ih2 j3 j4 j5 j6 j7 j8 j9 j10
case guard j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
  cases r <;> try simp at *
  case _ x sp sp' ξ h1 h2 h3 =>
    subst rin
    apply preservation_prefix_match_lemma j1 j2 j4 j8 h1 h2 h3
  case _ ℓ' r h =>
    subst h; simp at rin
    cases rin; case _ w h =>
    cases h; case _ h1 h2 =>
      subst h2; replace ih2 := ih2 r h1
      apply Judgment.guard j1 ih2 j3 j4 j5 j6 j7 j8 j9
case _ j1 j2 j3 ih1 ih2 =>
  cases r
  case _ =>
    simp at rin; subst rin
    cases j1; case _ j4 j5 j6 =>
      have lem := beta_type j6 j2
      subst j3; apply lem
  case _ x sp ixs ℓ' i1 i2 i3 i4 i5 =>
    simp at i4; replace i4 := Eq.symm i4
    rw [Option.bind_eq_some] at i4; simp at i4
    cases i4; case _ x' i4 =>
    cases i4; case _ sp' i4 =>
    cases i4; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3; subst i5
      simp at rin; cases rin; case _ w rin =>
      cases rin; case _ q1 q2 =>
        subst q2; subst i3
        have lem := preservation_inst_lemma j1 h1 i1 i2 q1
        rw [Term.apply_spine_peel_term]; constructor
        apply lem; apply j2; apply j3
  case _ T x sp t i1 i2 =>
    simp at i2; replace i2 := Eq.symm i2
    rw [Option.bind_eq_some] at i2; simp at i2
    cases i2; case _ x' i2 =>
    cases i2; case _ sp' i2 =>
    cases i2; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3; simp at rin; subst rin
      have lem := preservation_letterm_lemma j1 h1 i1
      rw [Term.apply_spine_peel_term]; constructor
      apply lem; apply j2; apply j3
  case _ ℓ' r h =>
    subst h; simp at rin
    cases rin; case _ f' h =>
    cases h; case _ h1 h2 =>
      subst h2; constructor
      apply ih1 r h1; apply j2; apply j3
case appt => sorry
case _ j1 j2 ih1 ih2 =>
  cases r <;> try simp at *
  case _ =>
    subst rin; cases j2; case _ =>
      apply j1
  case _ ℓ' r' h =>
    subst h; simp at rin
    cases rin; case _ z h =>
    cases h; case _ h1 h2 =>
      subst h2; constructor
      apply j1; apply ih2 r' h1
case _ j ih =>
  cases r <;> try simp at *
  case _ =>
    subst rin; cases j; case _ j1 j2 =>
      constructor; apply j1; apply j2
  case _ ℓ' r' h =>
    subst h; simp at rin
    cases rin; case _ z h =>
    cases h; case _ h1 h2 =>
      subst h2; constructor
      apply ih r' h1
case seq => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
