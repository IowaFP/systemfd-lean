import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

open LeanSubst

theorem preservation :
  G&Δ, Γ ⊢ t : T ->
  G ⊢ t ~> t' ->
  G&Δ, Γ ⊢ t' : T  := by
intro j h

sorry
