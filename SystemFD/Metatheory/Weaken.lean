import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

-- theorem rename_lift r (A : Term) :
--   (∀ x, [r.to](Γ d@ x) = Δ d@ (r x)) ->
--   ∀ x, [r.lift.to]((A::Γ) d@ x) = ([r.to]A::Δ) d@ (Ren.lift r x)
-- := by
-- intro h x; simp
-- cases x <;> simp at *
-- case _ => rw [Subst.lift_lemma]; simp
-- case _ x => rw [Subst.lift_lemma, <-h x]; simp

@[simp]
abbrev idx_ren (r : Ren) : JudgmentArgs v -> JudgmentArgs v :=
  match v with
  | .prf => λ (t, A) => ([r.to]t, [r.to]A)
  | .wf => λ () => ()

theorem rename (r : Ren) :
  Judgment v Γ idx ->
  ⊢ Δ ->
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  Judgment v Δ (idx_ren r idx)
:= by
intro j wf h
induction j <;> simp
any_goals apply wf
case _ Γ T t A j1 j2 ih1 ih2 => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
