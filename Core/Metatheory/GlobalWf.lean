import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Global

namespace Core
theorem GlobalWf.drop_wf : ∀ n, ⊢ G -> ⊢ G.drop n := by
intro n wf
induction wf generalizing n
case _ => simp; constructor
case _ g gwf wf ih =>
induction n
case _ => simp; constructor; assumption; assumption
case _ => simp; apply ih


theorem Global.drop_lookup {G : List Global} :
  ⊢ G ->
  G' = G.drop n ->
  lookup x G' = t ->
  lookup x G = t' ->
  t = t' := by
intro wf e h1 h2
induction n generalizing G G' t t' <;> simp at *
case zero => subst e; rw[h1] at h2; assumption
case succ n ih =>
  cases G <;> simp at *
  case nil =>
    simp [lookup] at h1 h2
    subst e h1 h2; simp [lookup]
  case cons g G =>
    apply @ih G' t t' G _ e h1 _
    cases wf; case _ wf _ => exact wf
    sorry



theorem Kinding.arbitrary_weakening_global : ⊢ G ->
  G' = G.drop n ->
  (G'& Δ ⊢ T : K) ->
  G&Δ ⊢ T : K := by
intro wf e j
induction j generalizing G
case var =>
  apply Kinding.var; assumption
case global x K Δ h =>
  apply Kinding.global
  simp [lookup_kind] at *;
  generalize zdef : lookup  x G = z at *
  generalize zdef' : lookup x G' = z' at *
  have lem := Global.drop_lookup wf e zdef' zdef
  subst z'; rw[lem] at h; assumption
case all j ih =>
  replace ih := @ih G wf e
  apply Kinding.all; assumption
all_goals (case _ ih1 ih2 =>
  replace ih1 := @ih1 G wf e
  replace ih2 := @ih2 G wf e
  constructor; assumption; assumption)


theorem EntryWf.get_openm {G} {Δ} {Γ} :
   ⊢ G ->
   EntryWf G (.openm x T) ->
   G&Δ, Γ  ⊢ g#x : T ∧
   ∃ b, G&Δ ⊢ T : .base b := by
intro wf h; cases h; case _ h =>
rcases h with ⟨n, p, h1, h2⟩
cases h2; case _ bk _ j =>
have lem := Kinding.closed_arbitrary_weakening (Δ' := Δ) (GlobalWf.drop_wf _ wf) j
generalize gdef : G.drop n = G' at *; symm at gdef
have lem := Kinding.arbitrary_weakening_global wf gdef lem
constructor
· apply Typing.global;
  assumption; assumption
· exists bk

-- theorem GlobalWf.weaken_defn :
--   ⊢ G ->
--   GlobalWf G (.defn x T t) ->
--   G&Δ, Γ ⊢ t : A ->
--   (.defn x T t :: G)&Δ, Γ ⊢ t : A := by
-- intro wf wfe j
-- induction j <;> (simp at *; cases wfe)
-- case var j => cases j <;> simp at *
-- case global j => sorry
-- case mtch => sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry
-- sorry

-- theorem GlobalWf.weaken_type :
--   ⊢ G ->
--   GlobalWf G e ->
--   Δ = [] ->
--   G&Δ ⊢ T : K ->
--   (e :: G)&Δ ⊢ T : K := by
-- intro wf wfe e j
-- cases wfe
-- case data =>
--   induction j
--   case var => subst e; simp at *
--   case global => sorry
--   case arrow => sorry
--   case all => sorry
--   case eq => sorry
--   case app => sorry

-- case opent K y _ h =>
--   induction j
--   case var => subst e; simp at *
--   case global x K' _ h1 =>
--     apply Kinding.global
--     unfold lookup_kind
--     generalize zdef : lookup x (.opent y K :: G) = z at *
--     cases z;
--     case _ =>
--       simp; simp [lookup] at zdef;
--       split at zdef
--       case _ e =>
--         subst e; simp [lookup_kind] at h1; rw[h] at h1; simp at h1
--       case _ =>  simp [lookup_kind] at h1; rw[zdef] at h1; simp at h1
--     case _ z =>
--       simp; unfold lookup at zdef
--       split at zdef
--       case _ e =>
--         replace e := eq_of_beq e; subst e; simp at zdef; simp[lookup_kind] at h1; rw[h] at h1; simp at h1
--       case _ => simp[lookup_kind] at h1; rw[zdef] at h1; simp at h1; assumption
--   case arrow j1 j2 ih1 ih2 =>
--     apply Kinding.arrow
--     apply ih1 e
--     apply ih2 e
--   case all ih1 =>
--     subst e
--     sorry -- booo!!
--   case eq => sorry
--   case app => sorry

-- case openm => sorry
-- case inst => sorry
-- case defn => sorry
-- case instty => sorry




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


theorem wf_lookup_type_sound :
  ⊢ G ->
  lookup_type G x = some T ->
  G&Δ, Γ ⊢ g#x : T := by
 intro wf h
 have lem := GlobalWf.types_have_base_kind (Δ := Δ) wf h;
 rcases lem with ⟨bk, lem⟩
 constructor; assumption;
 apply lem;

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

end Core
