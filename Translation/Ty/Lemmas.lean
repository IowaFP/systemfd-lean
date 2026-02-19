import Translation.Ty
import Translation.Global

import Core.Typing
import Surface.Typing
-- Translation preservies kinding relation

theorem Translation.KindEnv.sound {Δ : List Surface.Kind}{Δ' : List Core.Kind} :
  Surface.Kind.translateEnv Δ = Δ' ->
  (∀ (i : Nat) (K : Surface.Kind),
     (Δ[i]? = some K) -> ∃ K', ((Δ'[i]? = some K') ∧ K.translate = K')) := by
intro h1 i K h2
unfold Surface.Kind.translateEnv at h1
have lem := List.map_eq_iff.1 h1 i; rw[h2] at lem; simp at lem
exists K.translate

theorem Translation.Kind.sound_base {b : Surface.BaseKind}:
  ∃ b', (Surface.Kind.base b).translate = .base b' := by
cases b <;> simp at *
all_goals (subst K'; simp)

theorem Translation.Kind.sound_arrow {b1 b2 : Surface.Kind}:
  ∃ b1' b2', (Surface.Kind.arrow b1 b2).translate = .arrow b1' b2' := by simp

theorem Translation.Global.lookup_kind_sound :
  Surface.Global.translateEnv G = some G' ->
  Surface.lookup_kind G x = some K ->
  Core.lookup_kind G' x = some K'  := by
intro h1 h2
sorry


theorem Translation.Ty.sound :
  ⊢s G ->
  G&Δ ⊢s T : K ∧
  Surface.Global.translateEnv G = some G' ∧
  Surface.Kind.translateEnv Δ = Δ'  ->
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
  · simp [Surface.Kind.translateEnv] at t h2; rw[h2] at t; assumption
  · simp
  constructor; simp [Surface.Kind.translateEnv] at j; subst h2; simp [Surface.Kind.translateEnv]
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
