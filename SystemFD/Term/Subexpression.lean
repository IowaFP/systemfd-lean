import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Term.Shape

namespace Term

  inductive Subexpr : Term -> Term -> Prop where
  | refl : Subexpr s s
  | ctor1 : Subexpr s t -> Subexpr s (.ctor1 v t)
  | ctor2_1 : Subexpr s t1 -> Subexpr s (.ctor2 v t1 t2)
  | ctor2_2 : Subexpr s t2 -> Subexpr s (.ctor2 v t1 t2)
  | bind2_1 : Subexpr s t1 -> Subexpr s (.bind2 v t1 t2)
  | bind2_2 : s' = [S]s -> Subexpr s t2 -> Subexpr s' (.bind2 v t1 t2)
  | eq1 : Subexpr s t1 -> Subexpr s (.eq t1 t2 t3)
  | eq2 : Subexpr s t2 -> Subexpr s (.eq t1 t2 t3)
  | eq3 : Subexpr s t3 -> Subexpr s (.eq t1 t2 t3)
  | ite1 : Subexpr s t1 -> Subexpr s (.ite t1 t2 t3 t4)
  | ite2 : Subexpr s t2 -> Subexpr s (.ite t1 t2 t3 t4)
  | ite3 : Subexpr s t3 -> Subexpr s (.ite t1 t2 t3 t4)
  | ite4 : Subexpr s t4 -> Subexpr s (.ite t1 t2 t3 t4)
  | guard1 : Subexpr s t1 -> Subexpr s (.guard t1 t2 t3)
  | guard2 : Subexpr s t2 -> Subexpr s (.guard t1 t2 t3)
  | guard3 : Subexpr s t3 -> Subexpr s (.guard t1 t2 t3)
  | letterm1 : Subexpr s t1 -> Subexpr s (.letterm t1 t2 t3)
  | letterm2 : Subexpr s t2 -> Subexpr s (.letterm t1 t2 t3)
  | letterm3 : s' = [S]s -> Subexpr s t3 -> Subexpr s' (.letterm t1 t2 t3)

  theorem not_subexpr_ctor1 : ¬ Subexpr s (.ctor1 v t) -> ¬ Subexpr s t := by
  intro h1 h2
  apply h1; constructor; apply h2

  theorem not_subexpr_ctor2 :
    ¬ Subexpr s (.ctor2 v t1 t2) -> ¬ Subexpr s t1 ∧ ¬ Subexpr s t2
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.ctor2_1 h2
  case _ => intro h2; apply h1; apply Subexpr.ctor2_2 h2

  theorem not_subexpr_bind2 :
    ¬ Subexpr ([S]s) (.bind2 v t1 t2) -> ¬ Subexpr ([S]s) t1 ∧ ¬ Subexpr s t2
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.bind2_1 h2
  case _ =>
    intro h2; apply h1; apply Subexpr.bind2_2 rfl h2

  theorem not_subexpr_eq :
    ¬ Subexpr s (.eq t1 t2 t3) ->
    ¬ Subexpr s t1 ∧ ¬ Subexpr s t2 ∧ ¬ Subexpr s t3
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.eq1 h2
  apply And.intro; case _ => intro h2; apply h1; apply Subexpr.eq2 h2
  intro h2; apply h1; apply Subexpr.eq3 h2

  theorem not_subexpr_ite :
    ¬ Subexpr s (.ite t1 t2 t3 t4) ->
    ¬ Subexpr s t1 ∧ ¬ Subexpr s t2 ∧ ¬ Subexpr s t3 ∧ ¬ Subexpr s t4
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.ite1 h2
  apply And.intro; case _ => intro h2; apply h1; apply Subexpr.ite2 h2
  apply And.intro; case _ => intro h2; apply h1; apply Subexpr.ite3 h2
  intro h2; apply h1; apply Subexpr.ite4 h2

  theorem not_subexpr_guard :
    ¬ Subexpr s (.guard t1 t2 t3) ->
    ¬ Subexpr s t1 ∧ ¬ Subexpr s t2 ∧ ¬ Subexpr s t3
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.guard1 h2
  apply And.intro; case _ => intro h2; apply h1; apply Subexpr.guard2 h2
  intro h2; apply h1; apply Subexpr.guard3 h2

  theorem not_subexpr_letterm :
    ¬ Subexpr ([S]s) (.letterm t1 t2 t3) ->
    ¬ Subexpr ([S]s) t1 ∧ ¬ Subexpr ([S]s) t2 ∧ ¬ Subexpr s t3
  := by
  intro h1; apply And.intro
  case _ => intro h2; apply h1; apply Subexpr.letterm1 h2
  apply And.intro; case _ => intro h2; apply h1; apply Subexpr.letterm2 h2
  intro h2; apply h1; apply Subexpr.letterm3 rfl h2

  theorem subexpr_to_subst (σ : Subst Term) :
    Subexpr s t -> s.size = 0 -> (∀ n, s ≠ #n) -> Subexpr s ([σ]t)
  := by
  intro h1 h2 h3
  induction h1 generalizing σ <;> simp at *
  case refl s =>
    cases s; all_goals try solve | cases h2
    all_goals simp; try apply Subexpr.refl
    case _ x =>
      exfalso; apply h3 x rfl
  case _ ih =>
    apply Subexpr.ctor1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ctor2_1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ctor2_2
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.bind2_1
    apply ih σ h2 h3
  case bind2_2 s' s t2 v t1 j1 j2 ih =>
    have lem1 : [P]s' = [P][S]s := by rw [j1]
    simp at lem1
    rw [constant_non_variables_preserved_under_substitution P h2 h3] at lem1
    subst lem1; apply Subexpr.bind2_2 j1
    replace ih := ih (^σ) h2 h3; simp at ih
    apply ih
  case _ ih =>
    apply Subexpr.eq1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.eq2
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.eq3
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ite1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ite2
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ite3
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.ite4
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.guard1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.guard2
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.guard3
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.letterm1
    apply ih σ h2 h3
  case _ ih =>
    apply Subexpr.letterm2
    apply ih σ h2 h3
  case _ s' s t3 t1 t2 j1 j2 ih =>
    have lem1 : [P]s' = [P][S]s := by rw [j1]
    simp at lem1
    rw [constant_non_variables_preserved_under_substitution P h2 h3] at lem1
    subst lem1; apply Subexpr.letterm3 j1
    replace ih := ih (^σ) h2 h3; simp at ih
    apply ih

  theorem subexpr_from_subst :
    Subexpr s ([σ]b) -> s.size = 0 -> (∀ n, s ≠ #n) ->
      Subexpr s b ∨ (∃ i, ∃ t, σ i = .su t ∧ Subexpr s t)
  := by
  intro h1 h2 h3
  induction b generalizing s σ <;> simp at *
  case _ => apply Or.inl h1
  case _ i =>
    generalize zdef : σ i = z at *
    cases z <;> simp at *
    case _ j =>
      cases h1; exfalso
      apply h3 j rfl
    case _ t =>
      apply Or.inr; apply Exists.intro i
      apply Exists.intro t; apply And.intro zdef h1
  case _ => apply Or.inl h1
  case _ => apply Or.inl h1
  case _ v t ih =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih := ih h1 h2 h3
      cases ih
      case _ ih => apply Or.inl (Subexpr.ctor1 ih)
      case _ ih => apply Or.inr ih
  case _ v t1 t2 ih1 ih2 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.ctor2_1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ h1 =>
      replace ih2 := ih2 h1 h2 h3
      cases ih2
      case _ ih2 => apply Or.inl (Subexpr.ctor2_2 ih2)
      case _ ih2 => apply Or.inr ih2
  case _ v t1 t2 ih1 ih2 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.bind2_1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ s' q1 q2 =>
      have lem3 : [P]s = [P][S]s' := by rw [q1]
      simp at lem3
      have lem1 : s'.size = 0 := by
        rw [<-lem3]
        rw [constant_non_variables_preserved_under_substitution P h2 h3]
        rw [h2]
      have lem2 : ∀ n, ¬s' = #n := by
        intro n h; rw [<-lem3] at h
        rw [constant_non_variables_preserved_under_substitution P h2 h3] at h
        apply h3 n h
      replace ih2 := @ih2 s' (^σ); simp at ih2
      replace ih2 := ih2 q2 lem1 lem2
      cases ih2
      case _ ih2 => apply Or.inl; apply Subexpr.bind2_2 q1 ih2
      case _ ih2 =>
        cases ih2; case _ i ih2 =>
        cases ih2; case _ t ih2 =>
          cases i <;> simp at *
          case _ i =>
            apply Or.inr; apply Exists.intro i
            apply Exists.intro ([P]t)
            unfold Subst.compose at ih2; simp at ih2
            generalize zdef : σ i = z at *
            cases z <;> simp at *
            case _ t' =>
              rw [<-ih2.1]; simp
              have lem4 : [P][S]t' = [P]t := by rw [ih2.1]
              simp at *; rw [<-lem3] at ih2; rw [lem4]
              rw [constant_non_variables_preserved_under_substitution P h2 h3] at ih2
              apply subexpr_to_subst P ih2.2 h2 h3
  case _ ih1 ih2 ih3 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.eq1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ h1 =>
      replace ih2 := ih2 h1 h2 h3
      cases ih2
      case _ ih2 => apply Or.inl (Subexpr.eq2 ih2)
      case _ ih2 => apply Or.inr ih2
    case _ h1 =>
      replace ih3 := ih3 h1 h2 h3
      cases ih3
      case _ ih3 => apply Or.inl (Subexpr.eq3 ih3)
      case _ ih3 => apply Or.inr ih3
  case _ ih1 ih2 ih3 ih4 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.ite1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ h1 =>
      replace ih2 := ih2 h1 h2 h3
      cases ih2
      case _ ih2 => apply Or.inl (Subexpr.ite2 ih2)
      case _ ih2 => apply Or.inr ih2
    case _ h1 =>
      replace ih3 := ih3 h1 h2 h3
      cases ih3
      case _ ih3 => apply Or.inl (Subexpr.ite3 ih3)
      case _ ih3 => apply Or.inr ih3
    case _ h1 =>
      replace ih4 := ih4 h1 h2 h3
      cases ih4
      case _ ih4 => apply Or.inl (Subexpr.ite4 ih4)
      case _ ih4 => apply Or.inr ih4
  case _ ih1 ih2 ih3 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.guard1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ h1 =>
      replace ih2 := ih2 h1 h2 h3
      cases ih2
      case _ ih2 => apply Or.inl (Subexpr.guard2 ih2)
      case _ ih2 => apply Or.inr ih2
    case _ h1 =>
      replace ih3 := ih3 h1 h2 h3
      cases ih3
      case _ ih3 => apply Or.inl (Subexpr.guard3 ih3)
      case _ ih3 => apply Or.inr ih3
  case _ t1 t2 t3 ih1 ih2 ih3 =>
    cases h1
    case _ => cases h2
    case _ h1 =>
      replace ih1 := ih1 h1 h2 h3
      cases ih1
      case _ ih1 => apply Or.inl (Subexpr.letterm1 ih1)
      case _ ih1 => apply Or.inr ih1
    case _ h1 =>
      replace ih2 := ih2 h1 h2 h3
      cases ih2
      case _ ih2 => apply Or.inl (Subexpr.letterm2 ih2)
      case _ ih2 => apply Or.inr ih2
    case _ s' q1 q2 =>
      have lem3 : [P]s = [P][S]s' := by rw [q1]
      simp at lem3
      have lem1 : s'.size = 0 := by
        rw [<-lem3]
        rw [constant_non_variables_preserved_under_substitution P h2 h3]
        rw [h2]
      have lem2 : ∀ n, ¬s' = #n := by
        intro n h; rw [<-lem3] at h
        rw [constant_non_variables_preserved_under_substitution P h2 h3] at h
        apply h3 n h
      replace ih3 := @ih3 s' (^σ); simp at ih3
      replace ih3 := ih3 q2 lem1 lem2
      cases ih3
      case _ ih3 => apply Or.inl; apply Subexpr.letterm3 q1 ih3
      case _ ih3 =>
        cases ih3; case _ i ih3 =>
        cases ih3; case _ t ih3 =>
          cases i <;> simp at *
          case _ i =>
            apply Or.inr; apply Exists.intro i
            apply Exists.intro ([P]t)
            unfold Subst.compose at ih3; simp at ih3
            generalize zdef : σ i = z at *
            cases z <;> simp at *
            case _ t' =>
              rw [<-ih3.1]; simp
              have lem4 : [P][S]t' = [P]t := by rw [ih3.1]
              simp at *; rw [<-lem3] at ih3; rw [lem4]
              rw [constant_non_variables_preserved_under_substitution P h2 h3] at ih3
              apply subexpr_to_subst P ih3.2 h2 h3

  theorem subexpr_from_rename (r : Ren) :
    Subexpr s ([r.to]b) -> s.size = 0 -> (∀ n, s ≠ #n) -> Subexpr s b
  := by
  intro h1 h2 h3
  have lem := subexpr_from_subst h1 h2 h3
  cases lem
  case _ lem => apply lem
  case _ lem =>
    cases lem; case _ i lem =>
    cases lem; case _ t lem =>
      unfold Ren.to at lem; simp at lem

  theorem subexpr_from_beta :
    Subexpr s (b β[t]) -> s.size = 0 -> (∀ n, s ≠ #n) -> Subexpr s b ∨ Subexpr s t
  := by
  intro h1 h2 h3
  have lem := subexpr_from_subst h1 h2 h3
  cases lem
  case _ lem => apply Or.inl; apply lem
  case _ lem =>
    cases lem; case _ i lem =>
    cases lem; case _ z lem =>
    cases lem; case _ lem1 lem2 =>
      cases i <;> simp at *
      subst lem1; apply Or.inr lem2

end Term
