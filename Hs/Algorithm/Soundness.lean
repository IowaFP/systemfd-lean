import Hs.HsTerm
import Hs.Algorithm
import Hs.HsJudgment
import Hs.Compile

set_option maxHeartbeats 500000

theorem compile_soudness :
  (j : Γ ⊢s t : τ) ->
  compile Γ t τ j = .some t' ->
  CompileJ .term Γ ⟨t, τ; j, t'⟩ := by
intro j c;
unfold compile at c; split at c;
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
