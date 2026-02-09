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

theorem spine_has_base_type {t : Term} :
  G&Δ,Γ ⊢ t.apply sp : T ->
  ∃ B, G&Δ,Γ ⊢ t : B ∧ TypeMatch B T
:= by
  intro j; induction sp generalizing t T <;> simp [Term.apply] at *
  case nil =>
    exists T; apply And.intro j
    apply TypeMatch.refl
  case cons hd tl ih =>
    cases hd
    case type A =>
      obtain ⟨B, ih1, ih2⟩ := ih j
      cases ih1; case _ K C q1 q2 q3 =>
      subst q3; exists ∀[K]C
      apply And.intro q2
      apply TypeMatch.all A ih2
    case term a =>
      obtain ⟨B, ih1, ih2⟩ := ih j
      cases ih1; case _ A q1 q2 q3 =>
      exists A -:> B; apply And.intro q3
      apply TypeMatch.arrow ih2
    case oterm a =>
      obtain ⟨B, ih1, ih2⟩ := ih j
      cases ih1; case _ A q1 q2 q3 =>
      exists A -:> B; apply And.intro q3
      apply TypeMatch.arrow ih2

theorem SpineType.apply :
  G&Δ, Γ ⊢ t : T ->
  SpineType G Δ Γ sp B T ->
  G&Δ, Γ ⊢ t.apply sp : B := by

sorry
