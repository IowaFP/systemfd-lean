import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Global


theorem GlobalWf.weaken_type :
  ⊢ G ->
  GlobalWf G e ->
  G&[], [] ⊢ t : T ->
  (e :: G)&[], [] ⊢ t : T := by
intro wf wfe j
sorry


theorem GlobalWf.weaken_kind e :
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
