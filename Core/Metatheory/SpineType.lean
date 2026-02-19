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

namespace Core

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
intro j1 j2
induction j2 generalizing t <;> simp [Term.apply] at *
assumption
all_goals (rw[Spine.apply_spine_compose]; simp [Term.apply])
case term j2 j3 j4 j5 ih =>
  apply Typing.app j2 (ih j1) j3
case oterm j3 j4 j5 ih =>
 apply Typing.app j3 (ih j1) j4
case type j2 j3 e j4 ih =>
 apply Typing.appt (ih j1) j2 e


theorem Typing.replace_head_regular :
  ⊢ G ->
  a.spine = some (x, sp') ->
  G&Δ, Γ ⊢ a : T ->
  G&Δ, Γ ⊢ b : T ->
  G&Δ, Γ ⊢ a.apply sp : B ->
  G&Δ, Γ ⊢ b.apply sp : B := by
intro wf j1 j2 j3 j4
have lem := Typing.inversion_apply_spine wf j4
rcases lem with ⟨B', h1, h2, h3⟩
have e := Typing.spine_term_unique_typing j2 h2 j1; cases e
apply SpineType.apply j3 h1

end Core
