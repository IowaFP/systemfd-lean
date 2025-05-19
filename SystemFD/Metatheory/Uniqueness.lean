
import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.TypeMatch
import SystemFD.Metatheory.Shape
import SystemFD.Metatheory.Classification

theorem uniqueness_of_super_kind :
  t.IsKind -> Γ ⊢ t : A -> Γ ⊢ t : B -> A = B
:= by
intro h1 j1 j2
induction t generalizing Γ A B
case _ => cases j1
case _ x => cases h1
case _ => cases j1; cases j2; rfl
case _ => cases h1
case _ => cases h1
case _ v t1 t2 ih1 ih2 =>
  cases h1
  case _ h1 h2 =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      rfl
case _ v t1 t2 ih1 ih2 => cases h1
case _ =>
  cases j1; case _ q1 q2 q3 =>
  cases j2; case _ r1 r2 r3 =>
    rfl
case _ => cases h1
case _ => cases h1
case _ => cases h1

theorem uniqueness_of_kinds :
  t.IsType -> Γ ⊢ t : A -> Γ ⊢ t : B -> A = B
:= by
intro h1 j1 j2
induction t generalizing Γ A B
case _ => cases j1
case _ x =>
  cases j1; case _ q1 q2 =>
  cases j2; case _ r1 r2 =>
    generalize fdef : Γ d@ x = f at *
    unfold Frame.get_type at *
    cases f <;> simp at *
    all_goals (subst q2; subst r2; rfl)
case _ => cases j1; cases j2; rfl
case _ => cases h1
case _ => cases h1
case _ v t1 t2 ih1 ih2 =>
  cases h1
  case _ h1 h2 =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      have lem := classification_lemma q <;> simp at lem
      cases lem
      case _ lem =>
        have lem1 := kind_shape lem rfl
        have lem2 := type_shape q lem1
        replace ih1 := ih1 lem2 q r
        injection ih1 with _ e1 e2
      case _ lem =>
        cases lem; case _ _ lem =>
        cases lem.2; cases lem.1
case _ v t1 t2 ih1 ih2 =>
  cases h1
  case _ h1 h2 =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
  case _ h1 h2 =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
case _ =>
  cases j1; case _ q1 q2 q3 =>
  cases j2; case _ r1 r2 r3 =>
    rfl
case _ => cases h1
case _ => cases h1
case _ => cases h1

theorem uniqueness_prefix_match :
  PrefixTypeMatch Γ U V A ->
  PrefixTypeMatch Γ U V B ->
  A = B
:= by
intro j1 j2
induction V generalizing Γ U A B
any_goals try (
  case _ =>
    cases j1; case _ j1 =>
    cases j2; case _ j2 =>
      rfl
)
case _ v t1 t2 ih1 ih2 =>
  cases v
  any_goals try (
    case _ =>
      cases j1; case _ j1 =>
      cases j2; case _ j2 =>
        rfl
  )
  case _ =>
    cases j1
    case _ j1 =>
      cases j2
      case _ => rfl
      case _ B' j2 =>
        exfalso; apply no_valid_head_variable_with_all j1
    case _ j1 =>
    cases j2
    case _ j2 =>
      exfalso
      apply no_valid_head_variable_with_all j2
    case _ j2 =>
      replace ih2 := ih2 j1 j2
      have lem : [P][S]A = [P][S]B := by rw [ih2]
      simp at lem; apply lem
  case _ =>
    cases j1
    case _ j1 =>
      cases j2
      case _ => rfl
      case _ B' j2 =>
        exfalso; apply no_valid_head_variable_with_arrow j1
    case _ j1 =>
    cases j2
    case _ j2 =>
      exfalso
      apply no_valid_head_variable_with_arrow j2
    case _ j2 =>
      replace ih2 := ih2 j1 j2
      have lem : [P][S]A = [P][S]B := by rw [ih2]
      simp at lem; apply lem

theorem uniqueness_modulo_zero :
  ¬ Term.Subexpr `0 t -> Γ ⊢ t : A -> Γ ⊢ t : B -> A = B
:= by
intro js j1 j2
induction t generalizing Γ A B
case _ => cases j1
case _ x =>
  cases j1; case _ q1 q2 =>
  cases j2; case _ r1 r2 =>
    generalize fdef : Γ d@ x = f at *
    unfold Frame.get_type at *
    cases f <;> simp at *
    all_goals (subst q2; subst r2; rfl)
case _ => cases j1; cases j2; rfl
case _ =>
  exfalso; apply js; apply Term.Subexpr.refl
case _ v t ih =>
  replace js := Term.not_subexpr_ctor1 js
  cases v
  case _ =>
    cases j1; case _ A1 B1 q1 =>
    cases j2; case _ A2 B2 q2 =>
      replace ih := ih js q1 q2
      injection ih with e1 e2 e3
      subst e1; subst e2; subst e3; rfl
case _ v t1 t2 ih1 ih2 =>
  replace js := Term.not_subexpr_ctor2 js
  cases v
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      rfl
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      have lem1 := ih2 js.2 q3 r3
      injection lem1 with e1 e2 e3; subst e1
      injection e2 with _ w1 w2; subst w1; subst w2
      injection e3 with _ w1 w2; subst w1; subst w2
      have lem2 := classification_lemma q1; simp at lem2
      cases lem2
      case _ lem2 => rfl
      case _ lem2 =>
        cases lem2; case _ lem2 =>
          cases lem2.2; cases lem2.1
  case _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases j2; case _ r1 r2 r3 r4 =>
      have lem1 := ih2 js.2 q4 r4
      injection lem1 with e1 e2 e3; subst e1
      injection e2 with _ w1 w2; subst w1; subst w2
      injection e3 with _ w1 w2; subst w1; subst w2
      have lem2 := classification_lemma q2; simp at lem2
      cases lem2; case _ h => subst h; cases q1
      case _ lem2 =>
      cases lem2; case _ lem2 => rfl
      case _ lem2 =>
        cases lem2; case _ _ lem2 =>
          have lem3 := uniqueness_of_super_kind (kind_shape q1 rfl) q1 lem2.2
          subst lem3; cases lem2.1
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      rfl
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      replace ih1 := ih1 js.1 q r
      injection ih1 with _ e1 e2
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 js.1 q1 r1
      injection ih1 with _ e1 e2; subst e1; subst e2
      subst q3; subst r3; rfl
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 js.1 q1 r1
      injection ih1 with _ e1 e2; subst e1; subst e2
      subst q3; subst r3; rfl
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      replace ih2 := ih2 js.2 q r
      injection ih2 with _ e1 e2
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 js.1 q1 r1
      replace ih2 := ih2 js.2 q2 r2
      injection ih1 with e3 e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e2; subst e3
      rfl
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 js.1 q1 r1
      replace ih2 := ih2 js.2 q2 r2
      injection ih1 with e3 e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e1; subst e2
      injection e3 with _ e1 e2; subst e1; subst e2
      rfl
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 js.1 q1 r1
      replace ih2 := ih2 js.2 q2 r2
      injection ih1 with _ e1 e2;
      injection e1 with _ w1 w2; subst w1; subst w2
      injection e2 with _ _ w1; subst w1
      injection ih2 with _ e1 e2; subst e1; subst e2
      simp [*]
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      apply ih2 js.2 q r
case _ v t1 t2 ih1 ih2 =>
  have lem : `0 = [S]`0 := by simp
  rw [lem] at js
  replace js := Term.not_subexpr_bind2 js; simp at js
  cases v
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 js.2 q1 q2; subst ih2
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 js.2 q1 q2; subst ih2
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 js.2 q1 q2
      injection ih2 with _ e1 e2
      subst e1; subst e2; rfl
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 js.1 q2 r2
      replace ih2 := ih2 js.2 q3 r3
      injection ih1 with _ e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e1; subst e2
      rfl
case _ ih1 ih2 ih3 =>
  replace js := Term.not_subexpr_eq js
  cases j1; case _ q1 q2 q3 =>
  cases j2; case _ r1 r2 r3 =>
    rfl
case _ ih1 ih2 ih3 ih4 =>
  replace js := Term.not_subexpr_ite js
  cases j1; case _ q1 =>
  cases j2; case _ r1 =>
    replace ih4 := ih4 js.2.2.2 q1 r1; subst ih4; rfl
case _ ih1 ih2 ih3 =>
  replace js := Term.not_subexpr_guard js
  cases j1; case _ q1 q2 q3 q4 q5 q6 =>
  cases j2; case _ r1 r2 r3 r4 r5 r6 =>
    replace ih1 := ih1 js.1 q1 r1; subst ih1
    replace ih3 := ih3 js.2.2 q4 r4; subst ih3
    apply uniqueness_prefix_match q5 r5
case _ ih1 ih2 =>
  have lem : `0 = [S]`0 := by simp
  rw [lem] at js
  replace js := Term.not_subexpr_letterm js; simp at js
  cases j1; case _ q1 =>
  cases j2; case _ r1 =>
    replace ih2 := ih2 js.2.2 q1 r1;
    have lem : [P][S]A = [P][S]B := by rw [ih2]
    simp at lem; apply lem

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
    have lem1 := type_shape h2 (kind_shape h1 rfl)
    have lem := uniqueness_of_kinds lem1 h2 j2; subst lem
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
    have lem1 := type_shape j2' (kind_shape j2 rfl)
    have lem := uniqueness_of_kinds lem1 j2' h; subst lem
    cases j2

theorem uniqueness_modulo_neutral_form :
  t.neutral_form = .some (x, sp) ->
  Γ ⊢ t : A ->
  Γ ⊢ t : B ->
  A = B
:= by
intro j1 j2 j3
induction t generalizing Γ A B x sp
all_goals try simp at j1
case _ i =>
  cases j1; case _ h1 h2 =>
  subst h1; subst h2
  apply uniqueness_modulo_zero _ j2 j3
  intro h; cases h
case _ v t1 t2 ih1 ih2 =>
  cases v; all_goals try simp at j1
  case _ =>
    replace j1 := Option.bind_eq_some.1 j1
    cases j1; case _ w j1 =>
    cases w; case _ j sp' =>
    simp at j1; cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    subst h2; subst h3
    cases j2; case _ C q1 q2 =>
    cases j3; case _ U w1 w2 =>
    replace ih1 := ih1 h1 q2 w2
    injection ih1
  case _ =>
    replace j1 := Option.bind_eq_some.1 j1
    cases j1; case _ w j1 =>
    cases w; case _ j sp' =>
    simp at j1; cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    subst h2; subst h3
    cases j2; case _ C D q1 q2 q3 =>
    cases j3; case _ U V w1 w2 w3 =>
    replace ih1 := ih1 h1 q1 w1
    injection ih1 with _ e1 e2
    subst e1; subst e2
    subst q3; subst w3; rfl
  case _ =>
    replace j1 := Option.bind_eq_some.1 j1
    cases j1; case _ w j1 =>
    cases w; case _ j sp' =>
    simp at j1; cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    subst h2; subst h3
    cases j2; case _ C D q1 q2 q3 =>
    cases j3; case _ U V w1 w2 w3 =>
    replace ih1 := ih1 h1 q1 w1
    injection ih1 with _ e1 e2
    subst e1; subst e2
    subst q3; subst w3; rfl
