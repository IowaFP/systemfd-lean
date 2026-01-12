import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity


theorem reds_trans {Γ : Ctx Term} {L M R : Term} :
  L ⟨ Γ ⟩⟶⋆ M ->
  (M ⟨ Γ ⟩⟶⋆ R) ->
  L ⟨ Γ ⟩⟶⋆ R := by
intro s1 s2
induction s2
assumption
constructor; assumption; assumption

theorem redstar_choice₁ :
  (M ⟨ Γ ⟩⟶⋆ v) ->
  (M ⊕ N) ⟨ Γ ⟩⟶⋆ (v ⊕ N) := by
intro h1
induction h1
constructor
case _ y z _ r ih =>
  apply @RedStar.step Γ (M ⊕ N) (y ⊕ N) (z ⊕ N) ih
  apply Red.ctor2_congr1 (by simp) r;

theorem redstar_choice₂ :
  (N ⟨ Γ ⟩⟶⋆ v) ->
  (M ⊕ N) ⟨ Γ ⟩⟶⋆ (M ⊕ v) := by
intro h1
induction h1
constructor
case _ y z rs r ih =>
  apply @RedStar.step Γ (M ⊕ N) (M ⊕ y) (M ⊕ z) ih
  apply Red.ctor2_congr2 (by simp) r

theorem reds_choice_parallel {Γ : Ctx Term} {L L' R R'} :
  L ⟨ Γ ⟩⟶⋆ R ->
  L' ⟨ Γ ⟩⟶⋆ R' ->
  (L ⊕ L') ⟨ Γ ⟩⟶⋆ (R ⊕ R') := by
intro s1 s2
have lem1 : (L ⊕ L') ⟨ Γ ⟩⟶⋆ (R ⊕ L') := redstar_choice₁ s1
have lem2 : (R ⊕ L') ⟨ Γ ⟩⟶⋆ (R ⊕ R') := redstar_choice₂ s2
apply reds_trans lem1 lem2
