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

theorem redplus_is_redstar {Γ : Ctx Term} {N M : Term} :
  N ⟨Γ⟩⟶+ M ->
  N ⟨Γ⟩⟶⋆ M
:= by
sorry
-- intro h
-- induction h; constructor; assumption; assumption

theorem red_and_red_is_redplus {Γ : Ctx Term}{L M N : Term} :
  L ⟨Γ⟩⟶ M ->
  M ⟨Γ⟩⟶ N ->
  L ⟨Γ⟩⟶+ N
:= by
sorry
-- intro s1 s2
-- constructor; apply RedStar.step; apply RedStar.refl; assumption; assumption


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


theorem confluence {Γ : Ctx Term} {M v1 v2: Term} :
  (M ⟨ Γ ⟩⟶⋆ v1) ->
  (M ⟨ Γ ⟩⟶⋆ v2) ->
  Val Γ v1 ->
  Val Γ v2 ->
  v1 = v2 := by
sorry
