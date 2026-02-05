import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Global


theorem GlobalWf.weaken_defn :
  ⊢ G ->
  GlobalWf G (.defn x T t) ->
  G&Δ, Γ ⊢ t : A ->
  (.defn x T t :: G)&Δ, Γ ⊢ t : A := by
intro wf wfe j
induction j <;> (simp at *; cases wfe)
case var j => cases j <;> simp at *
case global j => sorry
case mtch => sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry



theorem GlobalWf.weaken_type :
  ⊢ G ->
  GlobalWf G e ->
  G&[] ⊢ T : K ->
  (e :: G)&[] ⊢ T : K := by
intro wf wfe j
sorry



theorem wf_lookup_kind_sound :
  ⊢ G ->
  lookup_type G x = some T ->
  G&[] ⊢ T : .base b := by
intro wf h
-- generalize lkdef : lookup_type G x = lk at *
induction wf generalizing x T
case _ => simp [lookup_type, lookup, default] at *
case _ G g gwf wf ih =>
  replace ih := @ih x T
  sorry


theorem wf_lookup_type_sound :
  ⊢ G ->
  lookup_type G x = some T ->
  G&Δ, Γ ⊢ g#x : T := by
 intro wf h
 constructor; assumption;
 sorry
 sorry
