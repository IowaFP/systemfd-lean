import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

theorem rename_lift r (A : Frame Term) :
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  ∀ x, ((A::Γ) d@ x).apply r.lift.to = (A.apply r.to::Δ) d@ (Ren.lift r x)
:= by sorry
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
induction j generalizing Δ r <;> simp at *
any_goals apply wf
case _ Γ T t A j1 j2 ih1 ih2 =>
  replace ih2 := ih2 r wf h
  have lem : ⊢ (Frame.datatype ([r.to]T) :: Δ) := by
    constructor; apply ih2; apply wf
  replace ih1 := @ih1 (Frame.datatype ([r.to]T) :: Δ) r.lift lem (rename_lift r (Frame.datatype T) h)
  rw [Subst.lift_lemma] at ih1; simp at ih1
  constructor; apply ih2; apply ih1
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
case _ => sorry
