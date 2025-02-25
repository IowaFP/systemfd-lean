import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Util

@[simp]
def get_instances : Ctx Term -> Nat -> List Term
| .nil, _ => []
| .cons _ _, 0 => []
| .cons (.inst #y t) Γ, (opm + 1) =>
  if y == opm then ([S]t) :: (List.map ([S]·) (get_instances Γ opm))
  else List.map ([S]·) (get_instances Γ opm)
| .cons _ Γ, (opm + 1) => List.map ([S]·) (get_instances Γ opm)

theorem get_instances_sound :
  t ∈ get_instances Γ x ->
  ∃ i, Γ d@ i = .inst #x t
:= by
intro j
induction Γ, x using get_instances.induct generalizing t
case _ => simp at *
case _ => simp at *
case _ y t' Γ opm h ih =>
  simp at *; subst h; simp at *
  cases j
  case _ j =>
    subst j; apply Exists.intro 0
    simp; unfold Frame.apply; simp
  case _ j =>
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
case _ y t' Γ opm h ih =>
  simp at *; split at j
  case _ h2 => exfalso; apply h h2
  case _ h2 =>
    simp at *
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
case _ hd Γ opm h ih =>
  cases hd <;> simp at *
  case inst z _ =>
    cases z <;> simp at *
    all_goals (
      cases j; case _ a j =>
      cases j; case _ h1 h2 =>
        subst h2
        replace ih := ih h1
        cases ih; case _ i ih =>
          apply Exists.intro (i + 1)
          simp; rw [ih]
          unfold Frame.apply; simp
    )
  all_goals (
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
  )
