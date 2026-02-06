import LeanSubst
import Core.Term
import Core.Term.Spine
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Metatheory.GlobalWf
import Core.Metatheory.Uniqueness
import Core.Metatheory.Inversion

theorem SpineType.apply :
  G&Δ, Γ ⊢ t : T ->
  SpineType G Δ Γ sp B T ->
  G&Δ, Γ ⊢ t.apply sp : B := by

sorry
