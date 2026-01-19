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

theorem Value.sound : Value G t -> ∀ t', ¬ (G ⊢ t ~> t') := by
  intro j; induction j <;> intro t' r
  case app x sp t j1 j2 j3 ih =>
    cases t
    all_goals try simp [Term.spine] at j1
    case global y =>
      rcases j1 with ⟨e1, e2⟩; subst e1 e2
      cases r; case _ z sp T tl tl' q1 q2 q3 q4 q5 q6 q7 q8 =>
      simp [Term.spine] at q7
      rcases q7 with ⟨e1, e2⟩; subst e1 e2; simp at *
      cases j3
      case _ j3 =>

        sorry
      case _ j3 =>
        sorry
    case ctor1 c t =>
      cases c <;> simp [Term.spine] at j1
      case appt =>
        sorry
    case ctor2 c t1 t2 =>
      cases c <;> try simp [Term.spine] at j1
      case app => sorry
      -- case appo =>
      --   replace j1 := Eq.symm j1
      --   rw [Option.bind_eq_some_iff] at j1
      --   rcases j1 with ⟨q, e1, e2⟩
      --   rcases q with ⟨y, sp'⟩; simp at e2
      --   rcases e2 with ⟨e2, e3⟩; subst e2 e3
      --   sorry
  case choice t1 t2 j1 j2 ih1 ih2 =>
    cases r <;> simp at *
    case inst h _ _ => simp [Term.spine] at h
    case ctor2_congr1 r _ => apply ih1 _ r
    case ctor2_congr2 r _ => apply ih2 _ r
  all_goals
    cases r <;> simp [Term.spine] at *
