import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.Shape

set_option maxHeartbeats 500000

@[simp]
abbrev WfKindCompleteLemmaType : (v : JudgmentVariant) -> Ctx Term -> JudgmentArgs v -> Prop
| .prf => λ Γ => λ (t, A) => A = □ -> Γ ⊢ t : A -> wf_kind t = .some ()
| .wf  => λ _ => λ () => true

theorem wf_kind_complete_lemma :
  Judgment v Γ idx ->
  WfKindCompleteLemmaType v Γ idx
:= by
intro j; induction j <;> simp at *
case letterm j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  intro h1 h2; subst h1
  cases j4
case var Γ x _ j1 j2 _  =>
  intro h1 h2; subst h1
  have lem := frame_wf_by_index x j1
  generalize zdef : Γ d@ x = z at *
  cases lem
  all_goals (
    unfold Frame.get_type at j2; simp at j2
    try (subst j2; case _ j => cases j)
  )
  all_goals case _ z1 z2 => subst j2; cases z1
case allk j1 j2 ih1 ih2 =>
  intro h; cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some]; apply Exists.intro ()
  apply And.intro (ih1 h1)
  rw [Option.bind_eq_some]; apply Exists.intro ()
  apply And.intro (ih2 h2) rfl
case appk j1 j2 ih1 ih2 =>
  intro h1 h2; subst h1
  have lem := super_kind_shape_lemma j1; simp at lem
  apply lem.2
  apply Term.Subexpr.ctor2_2
  apply Term.Subexpr.refl
case ite j1 j2 ih1 ih2 ih3 ih4 ih5 ih6 =>
  intro h1 h2; subst h1
  cases j1
case guard j ih1 ih2 ih3 ih4 ih5 =>
  intro h1 h2; subst h1
  cases j
case app j1 j2 j3 ih1 ih2 =>
  intro h1 h2; subst h1
  have lem := super_kind_equal_beta j3
  cases lem
  case _ lem =>
    subst lem
    have lem := super_kind_shape_lemma j1; simp at lem
    apply lem.2
    apply @Term.Subexpr.bind2_2 _ □ _ _ _; simp
    apply Term.Subexpr.refl
  case _ lem =>
    cases lem; case _ e1 e2 =>
    subst e1; subst e2
    cases h2; case _ j _ => cases j
case appt j1 j2 j3 ih1 ih2 =>
  intro h1 h2; subst h1
  have lem := super_kind_equal_beta j3
  cases lem
  case _ lem =>
    subst lem
    have lem := super_kind_shape_lemma j1; simp at lem
    apply lem.2
    apply @Term.Subexpr.bind2_2 _ □ _ _ _; simp
    apply Term.Subexpr.refl
  case _ lem =>
    cases lem; case _ e1 e2 =>
    subst e1; subst e2
    cases h2; case _ j _ => cases j
case cast j1 j2 ih1 ih2 =>
  intro h j; subst h
  have lem := super_kind_shape_lemma j2; simp at lem
  apply lem.2
  apply Term.Subexpr.eq3
  apply Term.Subexpr.refl
case empty j _ _ =>
  intro h _; subst h
  cases j
case choice j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  intro h1 h2; subst h1
  cases j2
