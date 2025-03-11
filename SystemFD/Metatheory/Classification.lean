import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Substitution
import SystemFD.Metatheory.Uniqueness

@[simp]
abbrev class_idx (t A : Term) : JudgmentArgs v :=
  match v with
  | .prf => (t, A)
  | .wf => ()

@[simp]
abbrev ClassType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (_, A) => A = .kind ∨ (Γ ⊢ A : .kind) ∨ (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K)
| .wf => λ () => ∀ x T, Frame.get_type (Γ d@ x) = .some T -> Γ ⊢ T : .kind ∨ (Γ ⊢ T : ★)

theorem classification_lemma : Judgment v Γ ix -> ClassType Γ v ix := by
intro j; induction j <;> simp at *
all_goals (try simp [*])
case wfnil =>
  intro T h; unfold Frame.get_type at h
  simp at h
case wfempty j1 ih1 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_empty ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_empty ih1
case _ j1 j2 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inr
      apply weaken_type j1 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_type j1 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_type j1 ih1
case _ j1 j2 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inl
      apply weaken_kind j1 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_kind j1 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_kind j1 ih1
case _ j1 j2 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inl
      apply weaken_datatype j1 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_datatype j1 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_datatype j1 ih1
case _ j1 j2 j3 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inr
      apply weaken_ctor j1 j3 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_ctor j1 j3 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_ctor j1 j3 ih1
case _ j1 j2 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inl
      apply weaken_opent j1 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_opent j1 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_opent j1 ih1
case _ j1 j2 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inr
      apply weaken_openm j1 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_openm j1 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_openm j1 ih1
case _ j1 j2 j3 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inr
      apply weaken_insttype j1 j3 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih1 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_insttype j1 j3 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_insttype j1 j3 ih1
case _ j1 j2 j3 ih1 ih2 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih2 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_inst j1 j2 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_inst j1 j2 ih1
case _ j1 j2 j3 ih1 ih2 ih3 =>
  intro x T h1
  cases x <;> simp at *
  case _ =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; unfold Frame.get_type at h1; simp at h1
      subst h1; apply Or.inr
      apply weaken_term j1 j2 j1
  case _ x =>
    cases h1; case _ a h1 =>
    cases h1; case _ h1 h2 =>
      subst h2; replace ih1 := ih2 x a h1
      cases ih1
      case _ ih1 =>
        apply Or.inl; apply weaken_term j1 j2 ih1
      case _ ih1 =>
        apply Or.inr; apply weaken_term j1 j2 ih1
case _ j _ _ _ _ =>
  apply Or.inr; apply Or.inr; apply Exists.intro ★
  apply And.intro _; apply j
  constructor; apply judgment_ctx_wf j
case _ Γ x T j1 j2 ih =>
  replace ih := ih x T (Eq.symm j2)
  cases ih
  case _ ih => apply Or.inr; apply Or.inl; apply ih
  case _ ih =>
    apply Or.inr; apply Or.inr
    exists ★; apply And.intro
    constructor; apply j1
    apply ih
case _ j _ _ _ =>
  apply Or.inl; constructor;
  apply judgment_ctx_wf j
case _ ih =>
  apply Or.inr; apply Or.inl
  cases ih
  case _ ih =>
    cases ih
    case _ ih => apply ih
  case _ ih =>
  cases ih; case _ K ih =>
    cases ih.2
    case _ ih1 ih2 => apply ih2
case _ j _ _ _ =>
  apply Or.inl; constructor
  apply judgment_ctx_wf j
case _ j _ _ _ _ ih =>
  apply Or.inr; apply Or.inr
  cases ih
  case _ ih =>
    apply Exists.intro ★; apply And.intro
    apply ih; apply j
  case _ ih =>
  cases ih; case _ K ih =>
    apply Exists.intro ★; apply And.intro
    constructor; apply judgment_ctx_wf j
    apply j
case _ j ih1 ih2 _ =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j
  apply j
case _ a _ _ _ _ ih1 ih2 =>
  cases ih2
  case _ ih2 => cases ih2
  case _ ih2 =>
  cases ih2; case _ K ih2 =>
  cases ih2; case _ ih2 ih3 =>
  cases ih3; case _ q1 q2 =>
    apply Or.inr; apply Or.inr; apply Exists.intro ★
    apply And.intro; assumption;
    have lem : ((★ β[a]) = ★) := by simp
    rw[<-lem];
    apply beta_empty; assumption
case _ j _ _ _ =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j
  apply j
case _ j1 j2 ih1 ih2 =>
  cases ih2
  case _ ih2 => cases ih2
  case _ ih2 =>
  cases ih2; case _ K ih2 =>
  cases ih2; case _ ih2 ih3 =>
  cases ih3; case _ q1 q2 =>
    apply Or.inr; apply Or.inr
    apply Exists.intro ★; apply And.intro
    apply ih2; apply beta_kind q2 j1
case _ ih =>
  cases ih
  case _ ih => cases ih
  case _ ih =>
  cases ih; case _ K ih =>
  cases ih; case _ ih1 ih2 =>
  cases ih2; case _ K ih2' _ ih2 =>
    apply Or.inr; apply Or.inr
    apply Exists.intro K; apply And.intro
    apply ih2'; apply ih2
case _ K _ j1 j2 _ _ =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j1
  constructor; apply j1
  apply j2; apply j2
case _ ih =>
  cases ih
  case _ ih => cases ih
  case _ ih =>
  cases ih; case _ K ih =>
  cases ih; case _ ih1 ih2 =>
  cases ih2; case _ K ih2 ih3 ih4 =>
    apply Or.inr; apply Exists.intro ★
    apply And.intro; constructor
    apply judgment_ctx_wf ih1
    constructor; apply ih2
    apply ih4; apply ih3
case _ j1 _ ih1 ih2 =>
  cases ih1
  case _ ih1 => cases ih1
  case _ ih1 =>
  cases ih1; case _ K ih1 =>
  cases ih1; case _ ih1 ih1' =>
  cases ih1'; case _ K1 q1 q2 q3 =>
    cases ih2
    case _ ih2 => cases ih2
    case _ ih2 =>
    cases ih2; case _ K ih2 =>
    cases ih2; case _ ih2 ih2' =>
    cases ih2'; case _ K2 w1 w2 w3 =>
      have lem := uniqueness_of_types q3 w2; subst lem
      apply Or.inr; apply Exists.intro ★
      apply And.intro; constructor
      apply judgment_ctx_wf j1
      constructor; apply q1
      apply q2; apply w3
case _ j1 j2 j3 j4 j5 j6 _ _ ih _ _ _ =>
  cases ih
  case _ ih =>
    cases ih
    case _ ih1 ih2 =>
      apply Or.inr; apply Exists.intro ★
      apply And.intro; constructor
      apply judgment_ctx_wf j1
      constructor; apply ih2
      constructor; apply j1; apply j4
      constructor; apply j2; apply j5
  case _ ih =>
  cases ih; case _ K ih =>
  cases ih; case _ ih1 ih2 =>
    cases ih2; cases ih1
case _ j1 j2 j3 j4 j5 j6 _ _ _ _ _ _ =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j1
  apply Judgment.eq _; constructor
  apply j1; apply j4; constructor
  apply j2; apply j5; constructor
  apply judgment_ctx_wf j1
case _ j1 j2 _ ih _ _ =>
  cases ih
  case _ ih =>
    cases ih; case _ ih1 ih2 =>
      apply Or.inr; apply Exists.intro ★
      apply And.intro; constructor
      apply judgment_ctx_wf j1
      apply Judgment.eq _; apply j1; apply j2
      constructor; apply ih1; apply ih2
  case _ ih =>
  cases ih; case _ K ih =>
  cases ih; case _ ih1 ih2 =>
    cases ih2; cases ih1
case _ j1 j2 j3 j4 _ _ _ ih =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j1
  constructor; apply j1; apply j2
  apply j3
case _ j1 j2 _ _ _ _ =>
  apply Or.inr; apply Exists.intro ★
  apply And.intro; constructor
  apply judgment_ctx_wf j1
  apply Judgment.eq _; apply j1; apply j2
  constructor; apply judgment_ctx_wf j1
case _ j1 j2 _ _ _ _ _ ih1 ih2 =>
  cases ih1
  case _ ih1 => cases ih1
  case _ ih1 =>
  cases ih1; case _ K ih1 =>
  cases ih1; case _ ih1 ih3 =>
  cases ih3; case _ q1 q2 q3 =>
  cases q2; case _ w1 w2 =>
  cases q3; case _ r1 r2 =>
    have lem1 := beta_kind w2 j1; simp at lem1
    have lem2 := beta_kind r2 j2; simp at lem2
    apply Or.inr; apply Exists.intro ★
    apply And.intro; constructor
    apply judgment_ctx_wf j1
    apply Judgment.eq _; apply lem1; apply lem2
    constructor; apply judgment_ctx_wf j1

theorem kind_disjoint :
  Γ ⊢ t : A -> A = .kind ->
  ¬ (Γ ⊢ .kind : .kind) ∧ ¬ (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K)
:= by
intro j1 j2; subst j2
apply And.intro
case _ => intro h; cases h
case _ =>
  intro h
  cases h; case _ K h =>
  cases h; case _ h1 h2 =>
  cases h2

theorem type_disjoint :
  Γ ⊢ t : A -> Γ ⊢ A : .kind ->
  ¬ (A = .kind) ∧ ¬ (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K)
:= by
intro j1 j2
apply And.intro
case _ =>
  intro h; subst h; cases j2
case _ =>
  intro h
  cases h; case _ K h =>
  cases h; case _ h1 h2 =>
    have lem := uniqueness_of_types j2 h2; subst lem
    cases h1

theorem term_disjoint :
  Γ ⊢ t : A -> (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K) ->
  ¬ (A = .kind) ∧ ¬ (Γ ⊢ A : .kind)
:= by
intro j1 j2
have lem := classification_lemma j1; simp at lem
cases j2; case _ K j2 =>
cases j2; case _ j2 j2' =>
  apply And.intro
  case _ =>
    intro h; subst h
    cases j2'
  case _ =>
    intro h
    have lem := uniqueness_of_types j2' h; subst lem
    cases j2
