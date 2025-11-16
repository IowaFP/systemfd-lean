import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity


theorem reds_trans {Γ : Ctx Term} {L M R : Term} :
  L ⟨ Γ ⟩⟶⋆ M ->
  (M ⟨ Γ ⟩⟶⋆ R) ->
  L ⟨ Γ ⟩⟶⋆ R := by
intro s1 s2
induction s1
assumption
sorry

theorem reds_choice_parallel {Γ : Ctx Term} {L L' R R'} :
  L ⟨ Γ ⟩⟶⋆ R ->
  L' ⟨ Γ ⟩⟶⋆ R' ->
  (L ⊕ L') ⟨ Γ ⟩⟶⋆ (R ⊕ R') := by sorry



theorem confluence {Γ : Ctx Term} {M v1 v2: Term} :
  (M ⟨ Γ ⟩⟶⋆ v1) ->
  (M ⟨ Γ ⟩⟶⋆ v2) ->
  Val Γ v1 ->
  Val Γ v2 ->
  v1 = v2 := by
sorry

theorem choice_lift_red_lhs :
  (M ⟨ Γ ⟩⟶⋆ v) ->
  (M ⊕ N) ⟨ Γ ⟩⟶⋆ (v ⊕ N) := by
intro h1
induction h1
constructor
case _ y z _ _ ih =>
  apply @RedStar.step Γ (M ⊕ N) (y ⊕ N) (z ⊕ N) ih


  sorry

theorem choice_reduction_unqiue {Γ : Ctx Term} {M N v: Term}:
  (M ⟨ Γ ⟩⟶⋆ v) ->
  (N ⟨ Γ ⟩⟶⋆ `0) ->
  (M ⊕ N) ⟨ Γ ⟩⟶⋆ v := by
intro h1 h2

have lem1 : (M ⊕ N) ⟨ Γ ⟩⟶⋆ (M ⊕ `0) := by sorry
have lem2 : (M ⊕ `0) ⟨ Γ ⟩⟶⋆ v := by
  apply @RedStar.step Γ (M ⊕ `0) (v ⊕ `0) v
  sorry
  constructor

sorry
