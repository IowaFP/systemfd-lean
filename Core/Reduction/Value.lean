import LeanSubst
import Core.Term
import Core.Reduction.Definition
import Core.Reduction.Congr

open LeanSubst

@[simp]
theorem Value.not_zero : ¬ Value G `0 := by
  intro j; cases j
  case _ x sp j1 j2 j3 =>
  simp [Term.spine] at j3

theorem Value.spine_sound :
  some (x, sp) = t.spine ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> ∀ t', ¬ (G ⊢ t ~> t')) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> t.not_choice) ->
  is_stable x G ∨ OpenVarVal G x sp ->
  ∀ t', ¬ (G ⊢ t ~> t')
:= by
  intro h1 h2 h3 h4 t' r
  induction sp using List.reverse_ind generalizing x t t'
  case nil =>
    have lem := Spine.apply_eq h1
    rw [lem] at r; simp [Term.apply] at r
    cases r
    case inst y sp T tl tl' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
      simp [Term.spine] at q8
      rcases q8 with ⟨e1, e2⟩; subst e1 e2
      simp at q5
      cases h4
      case _ h4 =>
        unfold is_stable at h4
        rw [q1] at h4
        simp at h4
      case _ h4 =>
        replace h4 := h4.2 T q4; simp at h4
        omega
  case rcons hd tl ih =>
    cases t <;> try solve | simp [Term.spine] at h1
    case ctor1 v t =>
      cases v <;> try solve | simp [Term.spine] at h1
      case appt =>
        simp at h1
        rcases h1 with ⟨sp', e1, e2⟩
        rcases e1 with ⟨e1, e3⟩; subst e1 e3
        cases r <;> try solve | simp [Term.spine] at *
        case inst y sp T tl' tl'' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
          simp at q8; rcases q8 with ⟨sp'', e3, e4⟩
          subst e3; rw [<-e4] at e2; injection e2 with e2
          injection e2 with e2 e3; subst e2 e3
          cases h4
          case _ h4 =>
            unfold is_stable at h4
            rw [q1] at h4; simp at h4
          case _ h4 =>
            replace h4 := h4.2 T q4
            simp at h4 q5
            omega
        case ctor1_congr t1' _ r =>
          apply ih e2 _ _ _ _ r
          case _ =>
            intro e q1 t q2
            apply h2 e _ _ q2
            simp; apply Or.inl q1
          case _ => sorry
            -- cases h4
            -- case _ h4 => apply Or.inl h4
            -- case _ h4 =>
            --   apply Or.inr; apply And.intro
            --   apply h4.1; intro T q
            --   replace h4 := h4.2 T q
            --   simp at *; omega
          case _ =>
            sorry
    case ctor2 v t1 t2 =>
      cases v <;> try solve | simp [Term.spine] at h1
      case app b =>
      cases b <;> simp at h1
      case closed =>
        rcases h1 with ⟨sp', e1, e2⟩
        rcases e1 with ⟨e1, e3⟩; subst e1 e3
        cases r <;> try solve | simp [Term.spine] at *
        case inst y sp T tl' tl'' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
          simp at q8; rcases q8 with ⟨sp'', e3, e4⟩
          subst e3; rw [<-e4] at e2; injection e2 with e2
          injection e2 with e2 e3; subst e2 e3
          cases h4
          case _ h4 =>
            unfold is_stable at h4
            rw [q1] at h4; simp at h4
          case _ h4 =>
            replace h4 := h4.2 T q4
            simp at h4 q5
            omega
        case ctor2_congr1 t1' _ r =>
          apply ih e2 _ _ _ _ r
          case _ =>
            intro e q1 t q2
            apply h2 e _ _ q2
            simp; apply Or.inl q1
          case _ =>
            sorry
            -- cases h4
            -- case _ h4 => apply Or.inl h4
            -- case _ h4 =>
            --   apply Or.inr; apply And.intro
            --   apply h4.1; intro T q
            --   replace h4 := h4.2 T q
            --   simp at *; omega
          case _ =>
            sorry
      case «open» =>
        rcases h1 with ⟨sp', e1, e2⟩
        rcases e1 with ⟨e1, e3⟩; subst e1 e3
        cases r <;> try solve | simp [Term.spine] at *
        case inst y sp T tl' tl'' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
          simp at q8; rcases q8 with ⟨sp'', e3, e4⟩
          subst e3; rw [<-e4] at e2; injection e2 with e2
          injection e2 with e2 e3; subst e2 e3
          cases h4
          case _ h4 =>
            unfold is_stable at h4
            rw [q1] at h4; simp at h4
          case _ h4 =>
            replace h4 := h4.2 T q4
            simp at h4 q5
            omega
        case ctor2_congr1 t1' _ r =>
          apply ih e2 _ _ _ _ r
          case _ =>
            intro e q1 t q2
            apply h2 e _ _ q2
            simp; apply Or.inl q1
          case _ =>
            sorry
            -- cases h4
            -- case _ h4 => apply Or.inl h4
            -- case _ h4 =>
            --   apply Or.inr; apply And.intro
            --   apply h4.1; intro T q
            --   replace h4 := h4.2 T q
            --   simp at *; omega
          case _ =>
            sorry
        case ctor2_congr2 t2' _ r =>

          sorry
        case ctor2_absorb2 => sorry
        case ctor2_map2 c1 c2 _ _ =>
          replace h3 := h3 (.oterm (c1 `+ c2)) (by simp) (c1 `+ c2) rfl
          simp [Term.not_choice] at h3

theorem Value.sound : Value G t -> ∀ t', ¬ (G ⊢ t ~> t') := by
  intro j; induction j <;> intro t' r
  case app x sp t j1 j2 j3 j4 ih =>
    cases t
    all_goals try simp [Term.spine] at j1
    case global y =>
      rcases j1 with ⟨e1, e2⟩; subst e1 e2
      cases r; case _ z sp T tl tl' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
      simp [Term.spine] at q8
      rcases q8 with ⟨e1, e2⟩; subst e1 e2; simp at *
      cases j4
      case _ j4 =>
        unfold is_stable at j4
        exfalso; rw [q1] at j4; simp at j4
      case _ j4 =>
        rcases j4 with ⟨j4, j5⟩
        replace j5 := j5 _ q4; simp at j5
        rw [q5] at j5; cases j5
    case ctor1 c t =>
      cases c <;> try solve | simp [Term.spine] at j1
      case appt A =>
        simp at j1
        rcases j1 with ⟨sp', e1, e2⟩; subst e1
        apply spine_sound _ ih j3 j4 _ r
        simp; exact e2
    case ctor2 c t1 t2 =>
      cases c <;> try solve | simp [Term.spine] at j1
      case app b =>
        cases b
        case closed =>
          simp at j1
          rcases j1 with ⟨sp', e1, e2⟩; subst e1
          apply spine_sound _ ih j3 j4 _ r
          simp; exact e2
        case «open» =>
          simp at j1
          rcases j1 with ⟨sp', e1, e2⟩; subst e1
          apply spine_sound _ ih j3 j4 _ r
          simp; exact e2
  case choice t1 t2 j1 j2 ih1 ih2 =>
    cases r <;> simp at *
    case inst h _ _ => simp [Term.spine] at h
    case ctor2_congr1 r _ => apply ih1 _ r
    case ctor2_congr2 r _ => apply ih2 _ r
  all_goals
    cases r <;> simp [Term.spine] at *
