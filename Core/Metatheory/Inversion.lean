import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Util
import Core.Vec

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Metatheory.Closed
import Core.Metatheory.Uniqueness
import Core.Metatheory.Progress
import Core.Metatheory.Preservation


open Lilac
open LeanSubst

namespace Core

theorem typing_inversion_lookup_spine_type (wf : ⊢ G) :
  lookup_spine_type v G x = some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩ ->
  G&(Ks1.list ++ Ks2.list).reverse ⊢ R : ★
:= by
 intro h
 unfold lookup_spine_type at h
 generalize zdef : lookup x G = z at *
 cases z; simp at *
 case _ z =>
 have lem := EntryWf.from_lookup wf zdef
 have lem_name := lookup_name_agrees zdef; simp [Entry.name] at lem_name; subst lem_name
 cases z <;> simp [Entry.spine_type] at *
 · split at h <;> simp at *
   case _ h1 =>
   rcases h1 with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3; subst h
   cases lem;
   case _ lem _ =>
   cases lem; case _ e _ _ h _ =>
   subst e; simp at h; apply h
 · split at h <;> simp at *
   case _ h1 =>
   rcases h1 with ⟨e1, e2⟩; subst e1; subst e2; subst h
   cases lem; case _ h _ =>
   cases h; case _ e _ _ h =>
   subst e; simp at *; apply h
 · split at h <;> simp at *
   case _ h1 =>
   rcases h1 with ⟨e1, e2⟩; subst e1; subst e2; subst h
   cases lem; case _ h _ =>
   cases h; case _ e _ _ h _ =>
   subst e; simp at *; apply h


theorem terms_have_star_types (wf : ⊢ G):
  G&Δ, Γ ⊢ t : R ->
  G&Δ ⊢ R : ★
| .var _ h => h
| .defn _ h => h
| @Typing.spctor _ _ _ _ _ _ _ v _ _ _ _ _ _ _ _ _ h1 e1 e2 h2 h3 h4 h5 h6 h7 => by
  have lem := typing_inversion_lookup_spine_type wf h1
  cases v
  · subst e1; subst e2; simp at lem; simp;
    sorry
  · case _ c =>
    cases c
    subst e1; subst e2; simp at lem; simp; sorry
    sorry
| .mtch h1 h2 h3 h4 h5 => by
  replace h4 := h4 0;
  sorry
| .lam h1 h2 =>
  have lem := terms_have_star_types wf h2
  Kinding.arrow h1 lem
| .app h1 h2 => by
  have lem := terms_have_star_types wf h1
  cases lem; case _ lem =>
  apply lem
| .lamt h1 h2 => h1
| .appt h1 h2 e => by
  have lem := terms_have_star_types wf h1
  cases lem; case _ lem =>
  subst e
  apply Kinding.beta lem h2
| .refl j => Kinding.eq j j
| .cast h1 h2 h3 e => by
  subst e
  have lem := terms_have_star_types wf h2
  cases lem; case _ lem =>
  apply Kinding.beta h1 lem
| .prj h1 h2 => by
  have lem := terms_have_star_types wf h1
  cases h2
  · cases lem; case _ lem1 lem2 =>
    cases lem1; case _ lem1' _ _ lem1 =>
    cases lem2; case _ lem2 =>
    have e := Kinding.unique lem1' lem1; simp at e; subst e
    apply Kinding.eq; apply lem1
    sorry

  · cases lem; case _ lem1 lem2 =>
    cases lem1; case _ lem1' _ _ lem1 =>
    cases lem2; case _ lem2' _ _ lem2 =>

    have e := Kinding.unique lem1' lem2'; simp at e; subst e
    -- apply Kinding.eq; apply lem1
    sorry

  sorry
  sorry
| .allc  h1 => by
  have lem := terms_have_star_types wf h1
  cases lem; case _ lem1 lem2 =>
  apply Kinding.eq
  · apply Kinding.all lem1
  · apply Kinding.all lem2
| .apptc h1 h2 e1 e2 => by
  have lem1 := terms_have_star_types wf h1
  have lem2 := terms_have_star_types wf h2
  cases lem1; case _ lem1a lem1b =>
  cases lem2; case _ lem2a lem2b =>
  cases lem1a; case _ lem1a =>
  cases lem1b; case _ lem1b =>
  apply Kinding.eq
  · subst e1; apply Kinding.beta lem1a lem2a
  · subst e2; apply Kinding.beta lem1b lem2b


end Core
