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
  Δ = [] ->
  G&Δ ⊢ T : K ->
  (e :: G)&Δ ⊢ T : K := by
intro wf wfe e j
cases wfe
case data =>
  induction j
  case var => subst e; simp at *
  case global =>

    sorry
  case arrow => sorry
  case all => sorry
  case eq => sorry
  case app => sorry

case opent K y _ h =>
  induction j
  case var => subst e; simp at *
  case global x K' _ h1 =>
    apply Kinding.global
    unfold lookup_kind
    generalize zdef : lookup x (.opent y K :: G) = z at *
    cases z;
    case _ =>
      simp; simp [lookup] at zdef;
      split at zdef
      case _ e =>
        subst e; simp [lookup_kind] at h1; rw[h] at h1; simp at h1
      case _ =>  simp [lookup_kind] at h1; rw[zdef] at h1; simp at h1
    case _ z =>
      simp; unfold lookup at zdef
      split at zdef
      case _ e =>
        replace e := eq_of_beq e; subst e; simp at zdef; simp[lookup_kind] at h1; rw[h] at h1; simp at h1
      case _ => simp[lookup_kind] at h1; rw[zdef] at h1; simp at h1; assumption
  case arrow j1 j2 ih1 ih2 =>
    apply Kinding.arrow
    apply ih1 e
    apply ih2 e
  case all ih1 =>
    subst e
    sorry -- booo!!
  case eq => sorry
  case app => sorry

case openm => sorry
case inst => sorry
case defn => sorry
case instty => sorry




theorem GlobalWf.types_have_base_kind :
  ⊢ G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢ T : .base b := by
intro wf h
-- generalize lkdef : lookup_type G x = lk at *
induction wf generalizing x T
case _ => simp [lookup_type, lookup, default] at *
case _ G g gwf wf ih =>
  replace ih := @ih x T
  sorry


theorem wf_lookup_type_sound : -- needs weakning
  ⊢ G ->
  lookup_type G x = some T ->
  G&Δ, Γ ⊢ g#x : T := by
 intro wf h
 constructor; assumption;
 sorry
 sorry

theorem GlobalWf.lookup_defn_type_exists {G : List Global} {Δ : List Kind} {Γ : List Ty} :
  ⊢ G ->
  lookup_defn G x = some t ->
  ∃ T b, lookup_type G x = some T ∧ G&Δ ⊢ T : .base b := by
intro wf h
unfold lookup_defn at h
generalize zdef : lookup x G = z at *
sorry

theorem GlobalWf.lookup_defn_type {G : List Global} {Δ : List Kind} {Γ : List Ty} :
  ⊢ G ->
  lookup_defn G x = some t ->
  ∃ T b, G&Δ, Γ ⊢ g#x : T ∧ G&Δ, Γ ⊢ t : T ∧ G&Δ ⊢ T : .base b := by
intro wf h1
have lem := GlobalWf.lookup_defn_type_exists (G := G) (Δ := Δ) (Γ := Γ) wf h1
rcases lem with ⟨T, b, lem1, lem2⟩
exists T; exists b
constructor
· sorry
· sorry
