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
  (Surface.Kind.base b).translate  = K' ->
  ∃ b', K' = .base b' := by sorry

theorem Translation.Kind.sound_arrow :
  (Surface.Kind.arrow b1 b2).translate = K' ->
  ∃ b1' b2', K' = .arrow b1' b2' := by sorry

theorem Translation.Ty.sound :
  ⊢s G ->
  G&Δ ⊢s T : K ∧
  Surface.Global.translateEnv G = some G' ∧
  Surface.Kind.translateEnv Δ = Δ'  ->
  ∃ K' T', K.translate = K' ∧
  T.translate G' Δ' = some T' ∧
  G'&Δ' ⊢ T' : K' := by
intro wf j;
rcases j with ⟨j, j1, j2⟩
induction j <;> simp at *
case var Δ i K j =>
  replace j2 := Translation.KindEnv.sound j2 i K j
  rcases j2 with ⟨K', j', t⟩; rw[<-t] at j'
  constructor; assumption
case global =>

  sorry
case all =>
  sorry
case arrow ih1 ih2 =>
  replace ih1 := ih1 j2
  replace ih2 := ih2 j2
  rcases ih1 with ⟨A', t1, j1⟩
  rcases ih2 with ⟨B', t2, j2⟩
  exists (A' -:> B')
  rw[Option.bind_eq_some_iff]
  constructor
  · exists A'; constructor
    · assumption
    · sorry
  · sorry
case app => sorry
