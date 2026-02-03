import Core.Infer.Kind
import Core.Infer.KindSound
import Core.Infer.«Type»
import Core.Ty
import Core.Typing

theorem infer_type_sound :
  ⊢ G ->
  t.infer_type G Δ Γ = some T ->
  G&Δ, Γ ⊢ t : T := by
intro wf h
induction Δ, Γ, t using Term.infer_type.induct generalizing T <;> simp [Term.infer_type] at h
all_goals ( try
  case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  cases h
  replace h2 := infer_kind_sound h2 wf
  constructor; assumption; assumption )
case _ => -- match
  sorry
case _ => -- guard
  sorry
case _ ih => -- lam
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  cases h
  replace h1 := infer_kind_sound h1 wf
  replace h2 := base_kind_some h2; cases h2
  replace ih := ih h3
  replace h5 := base_kind_some h5; cases h5
  constructor; assumption; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  simp at h; rcases h with ⟨h6, h⟩; rcases h6 with ⟨h6, h7⟩
  subst h7; subst h; replace h6 := eq_of_beq h6;

  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
