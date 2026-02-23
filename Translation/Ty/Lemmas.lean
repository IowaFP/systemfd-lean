import Translation.Ty
import Translation.Global

import Core.Typing
import Surface.Typing

open LeanSubst

-- Translation preservies kinding relation

theorem Translation.KindEnv.sound {Δ : Surface.KindEnv} {Δ' : Core.KindEnv} :
  Δ.translate = Δ' ->
  (∀ (i : Nat) (K : Surface.Kind),
     (Δ[i]? = some K) -> ∃ K', ((Δ'[i]? = some K') ∧ K.translate = K')) := by
intro h1 i K h2; simp at *
unfold Surface.KindEnv.translate at h1
have lem := List.map_eq_iff.1 h1 i; simp [Surface.inst_getElem?_KindEnv] at *; rw[h2] at lem; simp at lem
assumption

theorem Translation.Kind.sound_base {b : Surface.BaseKind}:
  ∃ b', (Surface.Kind.base b).translate = .base b' := by
cases b <;> simp at *
all_goals (subst K'; simp)

theorem Translation.Kind.sound_arrow {b1 b2 : Surface.Kind}:
  ∃ b1' b2', (Surface.Kind.arrow b1 b2).translate = .arrow b1' b2' := by simp

theorem Translation.Global.lookup_kind_sound :
  G.translate = some G' ->
  Surface.lookup_kind G x = some K ->
  Core.lookup_kind G' x = some K'  := by
intro h1 h2
sorry


theorem Translation.Ty.sound :
  ⊢s G ->
  G&Δ ⊢s T : K ∧
  G.translate = some G' ∧
  Δ.translate = Δ'  ->

  ∃ K' T', K.translate = K' ∧
  T.translate G' Δ' = some T' ∧
  G'&Δ' ⊢ T' : K' := by
intro wf j;
rcases j with ⟨j, h1, h2⟩
induction j generalizing Δ' <;> simp at *
case var Δ i K j =>
  replace j2 := Translation.KindEnv.sound h2 i K j
  rcases j2 with ⟨K', j', t⟩; rw[<-t] at j'
  constructor; assumption
case global x K Δ h3 =>
  have lem := Translation.Global.lookup_kind_sound (K' := K.translate) h1 h3
  apply Core.Kinding.global
  apply lem
case all K Δ P j ih =>
  rcases ih with ⟨P', t, j⟩
  exists (∀[K.translate] P')
  rw[Option.bind_eq_some_iff]
  constructor
  exists P';
  constructor;
  · simp [Surface.KindEnv.translate] at t h2; rw[h2] at t; assumption
  · simp
  constructor; simp [Surface.KindEnv.translate] at j; subst h2; simp [Surface.KindEnv.translate]
  apply j
case arrow b1 _ b2 _ _ ih1 ih2 =>
  rcases ih1 with ⟨A', t1, j1⟩
  rcases ih2 with ⟨B', t2, j2⟩
  exists (A' -:> B'); subst h2
  rw[Option.bind_eq_some_iff]
  constructor
  · exists A'; constructor
    · assumption
    · rw[Option.bind_eq_some_iff]; exists B'
  · have lem1 := Translation.Kind.sound_base (b := b1)
    rcases lem1 with ⟨b1', lem1⟩
    have lem2 := Translation.Kind.sound_base (b := b2)
    rcases lem2 with ⟨b2', lem2⟩
    rw[lem1] at j1; rw[lem2] at j2
    apply Core.Kinding.arrow; assumption; assumption
case app ih1 ih2 =>
  rcases ih1 with ⟨f', t1, j1⟩
  rcases ih2 with ⟨a', t2, j2⟩
  exists (f' • a'); subst h2
  rw[Option.bind_eq_some_iff]
  constructor
  · exists f'; constructor
    · assumption
    · rw[Option.bind_eq_some_iff]; exists a'
  · apply Core.Kinding.app; assumption; assumption


theorem Translation.Ty.beta :
  ⊢s G ->
  G&Δ ⊢s a : K ->
  G&(K::Δ) ⊢s P : κ ->

  G.translate = some G' ->
  Δ.translate = Δ'  ->
  K.translate = K' ->

  a.translate G' Δ' = some a' ->
  P.translate G' (K'::Δ') = some P' ->

  (P[su a :: +0 :_]).translate G' Δ' = some (P'[su a' :: +0 :_]) := by sorry
