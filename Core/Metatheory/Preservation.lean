import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

open LeanSubst


theorem refl_spine_lemma :
  OpenVarVal G n sp ->
  ¬ (G&Δ, Γ ⊢ (g#n).apply sp : (A ~[K]~ B)) := by
intro h j

sorry

theorem refl_is_val :
  G&Δ, Γ ⊢ t : (A ~[K]~ B) ->
  Value G t ->
  ((t = refl! A) ∧ A = B) ∨ (∃ c1 c2, t = c1 `+ c2) := by
intro j h; induction h
any_goals (solve | cases j)
case refl =>
  cases j; constructor; simp
case choice t1 t2 _ _ ih1 ih2 =>
  cases j; apply Or.inr;  exists t1; exists t2
case app ih =>

  sorry

theorem well_typed_values_do_not_reduce :
  G&Δ, Γ ⊢ t : T ->
  Value G t -> ¬ G ⊢ t ~> t' := by
intro j h r
induction h generalizing T
case app => sorry
case choice ih1 ih2 => sorry
case lam => sorry
case lamt => sorry
case refl => sorry

theorem reduct_not_value :
  G ⊢ t ~> t' -> ¬ Value G t := by sorry

theorem preservation :
  G&Δ, Γ ⊢ t : T ->
  G ⊢ t ~> t' ->
  G&Δ, Γ ⊢ t' : T  := by
intro j h
induction j
case var => sorry
case global => sorry
case mtch => sorry
case guard => sorry
case lam => sorry
case app => sorry
case lamt => sorry
case appt => sorry
case cast => sorry
case refl => sorry
case sym => sorry
case seq => sorry
case appc => sorry
case arrowc => sorry
case fst => sorry
case snd => sorry
case allc => sorry
case apptc => sorry
case zero => cases h; simp at *; sorry
case choice => sorry
