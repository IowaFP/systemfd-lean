
import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx

theorem no_valid_head_variable_with_all :
  ¬ ValidHeadVariable (∀[A]B) test
:= by
intro h; unfold ValidHeadVariable at h
cases h; case _ x h =>
cases h; case _ h1 h2 =>
  simp at h1

theorem no_valid_head_variable_with_arrow :
  ¬ ValidHeadVariable (A -t> B) test
:= by
intro h; unfold ValidHeadVariable at h
cases h; case _ x h =>
cases h; case _ h1 h2 =>
  simp at h1

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
      exfalso
      apply no_valid_head_variable_with_all j1
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
      exfalso
      apply no_valid_head_variable_with_arrow j1
    case _ j1 =>
    cases j2
    case _ j2 =>
      exfalso
      apply no_valid_head_variable_with_arrow j2
    case _ j2 =>
      replace ih2 := ih2 j1 j2
      have lem : [P][S]A = [P][S]B := by rw [ih2]
      simp at lem; apply lem

theorem uniqueness_of_types :
  Γ ⊢ t : A -> Γ ⊢ t : B -> A = B
:= by
intro j1 j2
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
case _ v t ih =>
  cases v
  case _ =>
    cases j1; case _ K1 q1 q2 =>
    cases j2; case _ K2 r1 r2 =>
      rfl
  case _ =>
    cases j1; case _ A1 B1 q1 =>
    cases j2; case _ A2 B2 q2 =>
      replace ih := ih q1 q2
      injection ih with _ e1 e2
      subst e1; subst e2; rfl
  case _ =>
    cases j1; case _ K1 q1 q2 =>
    cases j2; case _ K2 r1 r2 =>
      replace ih := ih q2 r2
      injection ih with _ e1 e2
      injection e1 with _ v1 v2
      injection e2 with _ u1 u2
      subst v1; subst v2; subst u1; subst u2
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih := ih q1 q2
      injection ih with _ e1 e2
      injection e1 with _ u1 u2
      injection e2 with _ v1 v2
      subst u1; subst u2; subst v1; subst v2
      rfl
case _ v t1 t2 ih1 ih2 =>
  cases v
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      rfl
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      replace ih1 := ih1 q r
      injection ih1 with _ e1 e2
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 q1 r1
      injection ih1 with _ e1 e2; subst e1; subst e2
      subst q3; subst r3; rfl
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 q1 r1
      injection ih1 with _ e1 e2; subst e1; subst e2
      subst q3; subst r3; rfl
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      replace ih2 := ih2 q r
      injection ih2 with _ e1 e2
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 q1 r1
      replace ih2 := ih2 q2 r2
      injection ih1 with _ e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e2
      rfl
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 q1 r1
      replace ih2 := ih2 q2 r2
      injection ih1 with _ e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e1; subst e2
      rfl
  case _ =>
    cases j1; case _ q1 q2 =>
    cases j2; case _ r1 r2 =>
      replace ih1 := ih1 q1 r1
      replace ih2 := ih2 q2 r2
      injection ih1 with _ e1 e2;
      injection e1 with _ w1 w2; subst w1; subst w2
      injection e2 with _ _ w1; subst w1
      injection ih2 with _ e1 e2; subst e1; subst e2
      rfl
  case _ =>
    cases j1; case _ q =>
    cases j2; case _ r =>
      rfl
case _ v t1 t2 ih1 ih2 =>
  cases v
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 q1 q2; subst ih2
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 q1 q2; subst ih2
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      rfl
  case _ =>
    cases j1; case _ q1 =>
    cases j2; case _ q2 =>
      replace ih2 := ih2 q1 q2
      injection ih2 with _ e1 e2
      subst e1; subst e2; rfl
  case _ =>
    cases j1; case _ q1 q2 q3 =>
    cases j2; case _ r1 r2 r3 =>
      replace ih1 := ih1 q2 r2
      replace ih2 := ih2 q3 r3
      injection ih1 with _ e1 e2; subst e1; subst e2
      injection ih2 with _ e1 e2; subst e1; subst e2
      rfl
case _ ih1 ih2 ih3 ih4 =>
  cases j1; case _ q1 =>
  cases j2; case _ r1 =>
    replace ih4 := ih4 q1 r1; subst ih4; rfl
case _ ih1 ih2 ih3 =>
  cases j1; case _ q1 q2 q3 q4 q5 q6 =>
  cases j2; case _ r1 r2 r3 r4 r5 r6 =>
    replace ih1 := ih1 q1 r1; subst ih1
    replace ih3 := ih3 q4 r4; subst ih3
    apply uniqueness_prefix_match q5 r5
case _ ih1 ih2 =>
  cases j1; case _ q1 =>
  cases j2; case _ r1 =>
    replace ih2 := ih2 q1 r1;
    have lem : [P][S]A = [P][S]B := by rw [ih2]
    simp at lem; apply lem
