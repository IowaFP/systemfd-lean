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

private theorem idx_shift_lemma {ts : List Ty} {Δ' : List Kind} (h : ts.length = Δ'.length):
  (∀ (i : Nat) (h_1 : i < ts.length + 1), G&Δ ⊢ (t :: ts)[i] : (K' :: Δ')[i]'(by grind)) ->
  (∀ (i : Nat) (h_1 : i < ts.length), G&Δ ⊢ (ts)[i] : (Δ')[i])
 := by
intro h1 i hi
replace h1 := h1 (i + 1); simp at h1; replace h1 := h1 hi; apply h1


theorem Kinding.beta_many {Δ' : List Kind} {t : List Ty} (h : t.length = Δ'.length):
  G&(Δ' ++ Δ) ⊢ A : K ->
  (∀ i, (h : i < t.length) -> G&Δ ⊢ t[i] : Δ'[i]) ->
  σ = List.map su t ++ Subst.id Ty ->
  G&Δ ⊢ A[σ] : K
:= by
  intro j1 j2 e1
  induction Δ' generalizing A t σ <;> simp at *
  case nil => simp at h; subst h; subst e1; simp; apply j1
  case cons K' Δ' ih =>
    simp at h;
    have h' : t.length > 0 := by omega
    have lem := List.length_gt_zero_exists h'
    rcases lem with ⟨t, ts, e⟩; subst e; simp at *
    replace j2 := idx_shift_lemma (by simp at h; apply h) j2
    have lem : ts.length = Δ'.length := by simp at h; omega
    replace ih := @ih A[su t :: +0σ] (List.map su ts ++ Subst.id Ty) ts lem sorry j2 rfl
    rw[e1]
    sorry

  -- apply Kinding.subst Δ (su t::+0σ) _ j1
  -- intro i K h; cases i <;> simp at *
  -- case _ => subst h; exact j2
  -- case _ i => apply var h


theorem terms_have_star_types (wf : ⊢ G):
  G&Δ, Γ ⊢ t : R ->
  G&Δ ⊢ R : ★
| .var _ h => h
| .defn _ h => h
| .spctor (m1 := m1) (m2 := m2) (Ks1 := Ks1) (Ks2 := Ks2) (As := As) (Bs := Bs) (v := v) h1 e1 e2 h2 h3 h4 h5 h6 h7 => by
  have lem := typing_inversion_lookup_spine_type wf h1
  subst e2
  replace lem := lem.extend (Δ₂ := Δ)
  simp at lem; simp [List.map_reverse]; rw[<-List.append_assoc] at lem; rw[<-List.map_reverse]; rw[<-List.map_reverse]; rw[<-List.map_append];
  generalize Δ'def : Ks2.list.reverse ++ Ks1.list.reverse = Δ' at *
  generalize Zdef : Bs.list.reverse ++ As.list.reverse = Z at *
  have lem2 := Kinding.beta_many (Δ' := Δ') (t := Z) (σ := List.map su Z ++ Subst.id Ty) (by subst Δ'; subst Z; simp) lem
  simp at lem2;
  apply lem2; clear lem2
  intro i h; rw[<-Zdef] at h; simp at h;
  rw[<-Vec.list_reverse] at Δ'def Zdef;
  sorry
| .mtch (ζ := ζ) h1 h2 h3 h4 h5 => by
  replace h4 := h4 0
  have lem := terms_have_star_types wf h4;
  apply Kinding.strengthening_length (Δ' := (ζ 0)) lem
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
    cases lem1; case _ lem1' lem2' _ _ lem1 =>
    cases lem2; case _ lem2 =>
    have e := Kinding.unique lem1' lem1; simp at e; subst e
    have e := Kinding.unique lem2' lem2; simp at e; subst e
    apply Kinding.eq; apply lem1
    apply lem2

  · cases lem; case _ lem1 lem2 =>
    cases lem1; case _ lem1c lem1d _ _ _ =>
    cases lem2; case _ lem2c _ _ lem2d _ =>
    have e := Kinding.unique lem1c lem2c; simp at e; subst e
    have e := Kinding.unique lem1d lem2d; simp at e; subst e
    apply Kinding.eq lem1c lem1d

  · cases lem; case _ lem1 lem2 =>
    cases lem1; case _ lem1a lem1c =>
    cases lem2; case _ lem2b lem2d =>
    apply Kinding.eq lem1a lem2b

  · cases lem; case _ lem1 lem2 =>
    cases lem1; case _ lem1a lem1c =>
    cases lem2; case _ lem2b lem2d =>
    apply Kinding.eq lem1c lem2d

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


theorem arrow_type_value_inversion {G : GlobalEnv} (wf : ⊢ G) :
  Value G t ->
  G&Δ, Γ ⊢ t : (A -:> B) ->
  ∃ t', t = λ[A] t'
| .spctor not_openm, j => by
  let lem := spctor_inversion wf not_openm j
  exfalso; simp at lem
| @Value.lam _ T t , .lam _ _ => by exists t
| .lamt , j => by cases j
| .refl, j => by cases j

theorem all_type_value_inversion {G : GlobalEnv} (wf : ⊢ G) :
  Value G t ->
  G&Δ, Γ ⊢ t : (∀[K]B) ->
  ∃ t', t = Λ[K] t'
| .spctor not_openm, j => by
  let lem := spctor_inversion wf not_openm j
  exfalso; simp at lem
| .lam , j => by cases j
| @Value.lamt _ K t, .lamt _ _ => by exists t
| .refl, j => by cases j

theorem eq_type_value_inversion {G : GlobalEnv} (wf : ⊢ G) :
  Value G t ->
  G&Δ, Γ ⊢ t : (A ~[K]~ B) ->
  (t = refl! A) ∧ A = B
| .spctor not_openm, j => by
  let lem := spctor_inversion wf not_openm j
  exfalso; simp at lem
| .lam , j => by cases j
| .lamt, j => by cases j
| .refl, .refl _ => ⟨rfl, rfl⟩


theorem data_type_value_inversion {G : GlobalEnv} (wf : ⊢ G) :
  Value G t ->
  G&Δ, Γ ⊢ t : R ->
  Ty.data? v G R ->
  ∃ (na nb nc : Nat) (v : DataConst) (x : String) (As : Vec Ty na) (Bs : Vec Ty nb) (ts : Fun.Vec Term nc), t = .spctor (.data v) x As Bs ts
| .spctor (v := v) not_openm, .spctor h1 h2 h3 h4 h5 h6 h7 h8 h9 , j2 => by
  have lem := spctor_inversion wf not_openm (.spctor h1 h2 h3 h4 h5 h6 h7 h8 h9)
  simp [Ty.data?] at j2; rw[Option.isSome_iff_exists] at lem
  rcases lem with ⟨⟨R, tys⟩, lem⟩
  rw[lem] at j2; simp at j2
  simp; cases v
  simp at not_openm
  simp

| .lam , j1, j2 => by cases j1; simp [Ty.data?] at j2
| .lamt, j1, j2 => by cases j1; simp [Ty.data?] at j2
| .refl, j1, j2 => by cases j1; simp [Ty.data?] at j2


end Core
