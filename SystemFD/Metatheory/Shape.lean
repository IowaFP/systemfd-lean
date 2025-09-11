
import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Classification

import SystemFD.Algorithm

theorem super_kind_equal_subst : □ = [σ]t -> t = □ ∨ (∃ i, ∃ v, σ i = .su v ∧ v = □ ∧ t = #i) := by
intro h; induction t generalizing σ <;> simp at *
case _ x =>
  generalize zdef : σ x = z at *
  cases z <;> simp at *
  case _ v =>
    subst h; apply Exists.intro x
    apply Exists.intro □; simp [*]

theorem super_kind_equal_beta : □ = b β[t] -> b = □ ∨ (t = □ ∧ b = #0) := by
intro h; have lem := super_kind_equal_subst h
cases lem
case _ lem => apply Or.inl lem
case _ lem =>
cases lem; case _ i lem =>
cases lem; case _ v lem =>
cases lem; case _ lem1 lem2 =>
cases lem2; case _ lem2 lem3 =>
  subst lem2; subst lem3; cases i <;> simp at *
  subst h; rfl

@[simp]
abbrev SuperKindShapeLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, A) => ¬ Term.Subexpr □ t ∧ (A = □ ∨ ¬ Term.Subexpr □ A)
| .wf => λ () => ∀ n T, .some T = (Γ d@ n).get_type -> ¬ Term.Subexpr □ T

macro "super_kind_shape_lemma_ctx_nil_case!" ih:term : tactic => `(tactic| {
  intro n T h
  cases n <;> simp at *
  case _ =>
    rw [<-Frame.get_type_apply_commute] at h
    have lem := Frame.get_type_apply_eq_destruct h
    cases lem; case _ T' lem =>
    cases lem; case _ e lem =>
      unfold Frame.get_type at lem; simp at lem
  case _ n =>
    rw [<-Frame.get_type_apply_commute] at h
    have lem := Frame.get_type_apply_eq_destruct h
    cases lem; case _ T' lem =>
    cases lem; case _ e lem =>
      subst e; have lem2 := $ih _ _ lem
      intro h; apply lem2
      apply Term.subexpr_from_rename (λ x => x + 1) h (by simp) (by simp)
})

macro "super_kind_shape_lemma_ctx_cons_case!" ih1:term "," ih2:term : tactic => `(tactic| {
  intro n T h
  cases n <;> simp at *
  case _ =>
    unfold Frame.get_type at h; simp at h
    subst h; intro h
    replace h := Term.subexpr_from_rename (λ x => x + 1) h (by simp) (by simp)
    try (apply $ih2.1; assumption)
    try (apply $ih2; assumption)
  case _ n =>
    rw [<-Frame.get_type_apply_commute] at h
    have lem := Frame.get_type_apply_eq_destruct h
    cases lem; case _ T' lem =>
    cases lem; case _ e lem =>
      subst e; have lem2 := $ih1 _ _ lem
      intro h; apply lem2
      apply Term.subexpr_from_rename (λ x => x + 1) h (by simp) (by simp)
})

theorem super_kind_shape_lemma : Judgment v Γ a -> SuperKindShapeLemmaType Γ v a := by
intro j; induction j <;> simp at *
case _ =>
  intro T h; unfold Frame.get_type at h
  simp at h
case _ j ih => super_kind_shape_lemma_ctx_nil_case! ih
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_cons_case! ih1 , ih2
case _ ih1 ih2 => super_kind_shape_lemma_ctx_nil_case! ih2
case _ ih1 ih2 ih3 => super_kind_shape_lemma_ctx_cons_case! ih2 , ih3
case _ ih1 ih2 ih3 ih4 =>
  apply And.intro; intro h; cases h
  apply ih3.1; assumption
  apply ih1.1; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih2.1; assumption
  apply Or.inr ih4.1
case _ => intro h; cases h
case var x T j1 j2 ih =>
  apply And.intro; intro h; cases h
  replace ih := ih x T j2
  apply Or.inr ih
case _ ih1 ih2 =>
  intro h; cases h
  apply ih1; assumption
  apply ih2; assumption
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih1; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih2.1; assumption
  intro h; cases h
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih2.1; assumption
  intro h; cases h
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  apply ih1.1; assumption
  replace ih2 := Term.not_subexpr_ctor2 ih2.2
  apply Or.inr ih2.2
case _ ih1 ih2 ih3 =>
  apply And.intro; intro h; cases h
  apply ih3; assumption
  apply ih1.1; assumption
  apply ih2.1; assumption
  intro h; cases h
case _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  apply ih3.1; assumption
  apply ih4.1; assumption
  apply ih5.1; assumption
  apply Or.inr ih7.1
case _ ih1 ih2 ih3 ih4 ih5 =>
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  apply ih2.1; assumption
  apply ih3.1; assumption
  apply Or.inr; apply ih5.1
case _ ih1 ih2 ih3 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih1.1; assumption
  apply ih3.1
case _ e ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  apply ih1.1; assumption
  have lem : □ = [S]□ := by simp
  rw [lem] at ih2
  replace ih2 := Term.not_subexpr_bind2 ih2.2
  subst e; apply Or.inr; intro h
  replace h := Term.subexpr_from_beta h (by simp) (by simp)
  cases h
  case _ h => apply ih2.2 h
  case _ h => apply ih1.1 h
case _ ih1 ih2 ih3 =>
  apply And.intro; intro h; cases h
  apply ih2; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih1.1; assumption
  apply ih3.1
case _ e ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  apply ih1.1; assumption
  have lem : □ = [S]□ := by simp
  rw [lem] at ih2
  replace ih2 := Term.not_subexpr_bind2 ih2.2
  subst e; apply Or.inr; intro h
  replace h := Term.subexpr_from_beta h (by simp) (by simp)
  cases h
  case _ h => apply ih2.2 h
  case _ h => apply ih1.1 h
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  apply ih2.1; assumption
  replace ih2 := Term.not_subexpr_eq ih2.2
  apply Or.inr ih2.2.2
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih2; assumption
  apply ih1.1; assumption
  intro h; cases h
  apply ih2; assumption
  apply ih1.1; assumption
  apply ih1.1; assumption
case _ ih =>
  apply And.intro; intro h; cases h
  apply ih.1; assumption
  replace ih := Term.not_subexpr_eq ih.2
  intro h; cases h
  apply ih.1; assumption
  apply ih.2.2; assumption
  apply ih.2.1; assumption
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  apply ih2.1; assumption
  replace ih1 := Term.not_subexpr_eq ih1.2
  replace ih2 := Term.not_subexpr_eq ih2.2
  intro h; cases h
  apply ih1.1; assumption
  apply ih1.2.1; assumption
  apply ih2.2.2; assumption
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  apply ih2.1; assumption
  replace ih1 := Term.not_subexpr_eq ih1.2
  replace ih2 := Term.not_subexpr_eq ih2.2
  intro h; cases h
  case _ h =>
    apply ih1.1
    apply Term.Subexpr.ctor2_2; assumption
  case _ h =>
    cases h
    apply ih1.2.1; assumption
    apply ih2.2.1; assumption
  case _ h =>
    cases h
    case _ h =>
      apply ih1.2.2; assumption
    case _ h =>
      apply ih2.2.2; assumption
case _ ih1 ih2 =>
  have lem1 := Term.not_subexpr_eq ih1.2
  have lem2 := Term.not_subexpr_eq ih2.2
  apply And.intro; intro h
  cases h; apply ih1.1; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih2.1; assumption
  intro h; cases h
  case _ h => cases h
  case _ h =>
    cases h
    apply lem1.2.1; assumption
    case _ s' q1 q2 =>
      have lem : [P]□ = [P][S]s' := by rw [q1]
      simp at lem; rw [<-lem] at q2
      apply lem2.2.1; assumption
  case _ h =>
    cases h
    apply lem1.2.2; assumption
    case _ s' q1 q2 =>
      have lem : [P]□ = [P][S]s' := by rw [q1]
      simp at lem; rw [<-lem] at q2
      apply lem2.2.2; assumption
case _ ih1 ih2 ih3 =>
  apply And.intro; intro h; cases h
  have lem1 := Term.not_subexpr_ctor2 ih1.2
  apply lem1.1; assumption
  apply ih3.1; assumption
  intro h; cases h
  apply ih1.2; assumption
  apply ih1.1; assumption
  apply ih2.1; assumption
case _ ih1 ih2 ih3 ih4 =>
  apply And.intro; intro h; cases h
  apply ih3; assumption
  apply ih4.1; assumption
  intro h; cases h
  apply ih3; assumption
  apply ih1.1; assumption
  apply ih2.1; assumption
case _ ih1 ih2 ih3 =>
  have lem2 := Term.not_subexpr_eq ih3.2
  apply And.intro; intro h; cases h
  apply ih2; assumption
  case _ s' q1 q2 =>
    have lem : [P]□ = [P][S]s' := by rw [q1]
    simp at lem; rw [<-lem] at q2
    apply ih3.1; assumption
  intro h; cases h
  case _ h => cases h
  case _ h =>
    cases h
    apply ih2; assumption
    case _ s' q1 q2 =>
      have lem : [P]□ = [P][S]s' := by rw [q1]
      simp at lem; rw [<-lem] at q2
      apply lem2.2.1; assumption
  case _ h =>
    cases h
    apply ih2; assumption
    case _ s' q1 q2 =>
      have lem : [P]□ = [P][S]s' := by rw [q1]
      simp at lem; rw [<-lem] at q2
      apply lem2.2.2; assumption
case _ e1 e2 ih1 ih2 =>
  have lem0 : □ = [S]□ := by simp
  have lem1 := Term.not_subexpr_eq ih1.2
  have lem2 := Term.not_subexpr_eq ih2.2
  rw [lem0] at lem1
  have lem3 := Term.not_subexpr_bind2 lem1.2.1
  have lem4 := Term.not_subexpr_bind2 lem1.2.2
  simp at *
  apply And.intro; intro h; cases h
  apply ih1.1; assumption
  apply ih2.1; assumption
  intro h; cases h
  case _ h => cases h
  case _ h =>
    rw [e1] at h
    replace h := Term.subexpr_from_beta h (by simp) (by simp)
    cases h
    apply lem3.2; assumption
    apply lem2.2.1; assumption
  case _ h =>
    rw [e2] at h
    replace h := Term.subexpr_from_beta h (by simp) (by simp)
    cases h
    apply lem4.2; assumption
    apply lem2.2.2; assumption
case _ ih1 ih2 =>
  apply And.intro; intro h; cases h
  apply Or.inr; apply ih1.1
case _ ih1 ih2 ih3 ih4 =>
  apply And.intro; intro h; cases h
  apply ih2.1; assumption
  apply ih3.1; assumption
  apply Or.inr ih1.1

@[simp]
abbrev KindShapeLemmaType (_ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, A) => A = □ -> Term.IsKind t
| .wf => λ () => True

macro "kind_shape_lemma_app_case!" j1:term "," j2:term " , " j3:term : tactic => `(tactic| {
  intro h; subst h
  replace j3 := super_kind_equal_beta $j3
  cases j3
  case _ h =>
    subst h
    have lem := super_kind_shape_lemma $j1; simp at lem
    exfalso; apply lem.2
    apply @Term.Subexpr.bind2_2 _ □; simp
    constructor
  case _ h =>
    cases h; case _ e1 e2 =>
      subst e1; subst e2
      replace j2 := $j2
      cases j2
})

theorem kind_shape_lemma : Judgment v Γ a -> KindShapeLemmaType Γ v a := by
intro j; induction j <;> simp at *
case _ j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  intro h; rw [h] at j4
  cases j4
case _ => constructor
case _ j1 j2 _ =>
  intro h; subst h
  have lem := super_kind_shape_lemma j1; simp at lem
  exfalso; apply lem _ _ j2
  constructor
case _ ih1 ih2 => constructor; assumption; assumption
case _ j1 j2 _ _ =>
  intro h; subst h
  have lem := super_kind_shape_lemma j1; simp at lem
  exfalso; apply lem.2
  apply Term.Subexpr.ctor2_2
  constructor
case _ j1 j2 ih1 ih2 ih3 ih4 ih5 ih6 =>
  intro h; rw [h] at j1; cases j1
case _ j1 j2 ih1 ih2 ih3 ih4 ih5 =>
  intro h; rw [h] at j2; cases j2
case _ j1 j2 j3 _ _ => kind_shape_lemma_app_case! j1, j2, j3
case _ j1 j2 j3 _ _ => kind_shape_lemma_app_case! j1, j2, j3
case _ j _ _ =>
  intro h; subst h
  have lem := super_kind_shape_lemma j; simp at lem
  exfalso; apply lem.2
  apply Term.Subexpr.eq3
  constructor
case _ j _ _ =>
  intro h; rw [h] at j
  cases j
case _ j1 j2 j3 ih1 ih2 ih3 ih4 =>
  intro h; rw [h] at j1
  cases j1

theorem kind_shape : Γ ⊢ t : A -> A = □ -> Term.IsKind t := by
intro j1 j2
apply kind_shape_lemma j1 j2

theorem wf_kind_shape_sound : wf_kind k = .some u -> Term.IsKind k := by
intro h
induction k using wf_kind.induct generalizing u
case _ => constructor
all_goals (unfold wf_kind at h; simp at h)
case _ ih1 ih2 =>
  rw[Option.bind_eq_some] at h; cases h; case _ h =>
  cases h; case _ h =>
  rw[Option.bind_eq_some] at h; cases h; case _ h =>
  cases h; case _ h1 _ h2 _ =>
  -- cases e
  replace ih1 := ih1 h1
  replace ih2 := ih2 h2
  constructor; assumption; assumption


@[simp]
abbrev TypeShapeLemmaType (_ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, A) => Term.IsKind A -> Term.IsType t
| .wf => λ () => True

theorem type_shape_lemma : Judgment v Γ a -> TypeShapeLemmaType Γ v a := by
intro j
induction j <;> simp at *
case _ ih =>
  intro h; replace ih := ih (by constructor)
  exfalso; apply Term.is_kind_disjoint_is_type h ih
case _ => intro h; cases h
case _ wf gt _ =>
  intro h; constructor;
case _ => intro h; cases h
case _ j _ ih1 ih2 =>
  intro h; have lem := kind_shape j rfl
  constructor; apply lem
  apply ih2 h
case _ ih1 ih2 =>
  intro h; constructor
  apply ih1 h; apply ih2 h
case _ f A B a j1 j2 ih1 ih2 =>
  intro h
  have lem := classification_lemma j1; simp at lem
  cases lem
  case _ lem =>
    have lem2 := kind_shape lem rfl
    replace ih1 := ih1 lem2
    cases lem2; case _ q1 q2 =>
      replace ih2 := ih2 q1
      apply Term.IsType.app ih1 ih2
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; cases lem.1
case _ j1 j2 j3 ih1 ih2 ih3 =>
  intro h
  have lem := kind_shape j1 rfl
  constructor; apply lem
  apply ih2 lem; apply ih3 lem
case _ j _ _ _ _ _ _ _ =>
  intro h; cases h
  cases j; cases j
case _ j _ _ _ _ _ =>
  intro h; cases h
  cases j; cases j
case _ => intro h; cases h
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  intro h
  have lem1 := classification_lemma j1; simp at lem1
  cases lem1; case _ lem1 => cases lem1
  case _ lem1 =>
  cases lem1; case _ K lem1 =>
  cases lem1; case _ lem1 lem2 =>
  cases lem2; case _ q1 q2 =>
    have lem3 : B.IsKind ∨ a.IsKind := by
      subst j3; have lem := Term.is_kind_from_beta h
      apply Or.comm.1 lem
    cases lem3
    case _ lem3 => cases lem3; cases q2; cases q2
    case _ lem3 =>
      cases lem3
      case _ => cases j2; cases q1
      case _ => cases j2; cases q1
case _ => intro h; cases h
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  intro h
  have lem1 := classification_lemma j1; simp at lem1
  cases lem1; case _ lem1 => cases lem1
  case _ lem1 =>
  cases lem1; case _ K lem1 =>
  cases lem1; case _ lem1 lem2 =>
  cases lem2; case _ q1 q2 =>
    have lem3 : B.IsKind ∨ a.IsKind := by
      subst j3; have lem := Term.is_kind_from_beta h
      apply Or.comm.1 lem
    cases lem3
    case _ lem3 => cases lem3; cases q2; cases q2
    case _ lem3 =>
      cases lem3
      case _ => cases j2; cases q1
      case _ => cases j2; cases q1
case _ Γ t A c K B j1 j2 ih1 ih2  =>
  intro h
  have lem1 := classification_lemma j2; simp at lem1
  cases lem1; case _ lem1 => cases lem1
  case _ lem1 =>
  cases lem1; case _ K1 lem1 =>
  cases lem1; case _ lem1 lem2 =>
    cases h; cases lem2; case _ q1 q2 q3 => cases q3; cases q1
    cases lem2; case _ q1 q2 q3 => cases q3; cases q1
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ => intro h; cases h
case _ j1 j2 ih1 ih2 =>
  intro h; have lem := kind_shape j1 rfl
  replace ih2 := ih2 lem
  exfalso; apply Term.is_kind_disjoint_is_type h ih2
case _ j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  intro h; have lem := kind_shape j1 rfl
  replace ih2 := ih2 lem
  exfalso; apply Term.is_kind_disjoint_is_type h ih2

theorem type_shape : Γ ⊢ t : A -> A.IsKind -> t.IsType := by
intro j1 j2
apply type_shape_lemma j1 j2
