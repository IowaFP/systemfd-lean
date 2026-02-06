import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Metatheory.GlobalWf

theorem Typing.unique_var_typing :
  G&Δ,Γ ⊢ g#a : A ->
  G&Δ,Γ ⊢ g#a : T ->
  A = T := by
intro j1 j2
cases j1; cases j2
case _ j1 _ _ j2 =>
rw[j1] at j2; injection j2


theorem Typing.spine_term_unique_typing :
  G&Δ,Γ ⊢ a : A ->
  G&Δ,Γ ⊢ a : T ->
  a.spine = some (x, sp) ->
  A = T := by
intro j1 j2 h
induction j1 generalizing T sp
all_goals (try case _ h1 _ => cases j2; case _ h2 => rw[h1] at h2; cases h2; rfl)
all_goals (try simp [Term.spine] at h)
case _ b _ _ _ _ _ jf ja ih _ =>
  cases b
  all_goals (
    simp [Term.spine] at *
    rw[Option.bind_eq_some_iff] at h;
    rcases h with ⟨w, h1, h2⟩
    cases h2
    cases j2; case _ h =>
    have ih1 := ih h h1
    have ih2 := ih jf h1
    rw[ih1] at ih2
    cases ih2; cases ih1; rfl
  )
case _ jf ja e ih =>
  rw[Option.bind_eq_some_iff] at h
  rcases h with ⟨w, h1, h2⟩
  cases h2
  cases j2; case _ h e' =>
  have ih1 := ih h h1
  have ih2 := ih jf h1
  rw[ih1] at ih2
  cases ih2; cases ih1
  subst e'; subst e; rfl

theorem Kinding.unique :
  G&Δ ⊢ T : K ->
  G&Δ ⊢ T : K' ->
  K = K' := by
intro j1 j2;
induction j1 generalizing K'
all_goals (try
  case _ h1 =>
    cases j2; case _ h2 =>
    rw[h1] at h2; cases h2; rfl)
all_goals (try
  case _ => cases j2; rfl
)
case app jf ja ih1 ih2  =>
  cases j2; case _ j1 j2 =>
  replace ih2 := ih2 j1; cases ih2
  replace ih1 := ih1 j2; cases ih1; rfl
