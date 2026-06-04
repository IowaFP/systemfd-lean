import LeanSubst
import Core.Reduction
import Core.Eval.SmallStep


namespace Core

theorem eval_sound (Γ : GlobalEnv) :
  eval Γ M = some N ->
  Γ ⊢ M ~> N := by
intro h
fun_induction eval <;> simp at h
case _ =>  -- lookup defn
  sorry

case _ => -- openm
  sorry

case _ => -- openm
  sorry

case _ => -- mtch
  sorry

case _ => -- mtch
  sorry

case _ => -- Λ[K] t •[T]
  sorry

case _ => -- t •[T]
  sorry

case _ => -- λ t • t
  sorry

case _ => -- t • t
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry


end Core
