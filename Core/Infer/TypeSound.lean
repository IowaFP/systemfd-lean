import Core.Infer.Kind
import Core.Infer.KindSound
import Core.Infer.«Type»
import Core.Ty
import Core.Typing

theorem valid_data_type_sound :
  Ty.valid_data_type G x = some dt ->
  ValidTyHeadVariable x (is_data G) := by sorry

theorem valid_open_type_sound :
  Ty.valid_open_type G x = some dt ->
  ValidTyHeadVariable x (is_opent G) := by sorry

theorem valid_inst_type_sound :
  Term.valid_inst_type G x = some dt ->
  ValidHeadVariable x (is_instty G) := by sorry


theorem Ty.stable_type_match_sound :
  Ty.stable_type_match A R = .some () ->
  StableTypeMatch Δ A R := by sorry

theorem Ty.prefix_type_match_sound :
  Ty.prefix_type_match G A R = .some T ->
  PrefixTypeMatch G A R T := by sorry


theorem infer_type_sound :
  ⊢ G ->
  t.infer_type G Δ Γ = some T ->
  G&Δ, Γ ⊢ t : T := by
intro wf h
induction Δ, Γ, t using Term.infer_type.induct generalizing T <;> simp [Term.infer_type] at h
all_goals (try
  case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  cases h
  replace h2 := infer_kind_sound h2 wf
  constructor; assumption; assumption )
case _ ih1 ih2 ih3 ih4 => -- match
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨pat_sp, h3, h⟩
  simp at h; rcases h with ⟨h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h9, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h10, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h11, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace h4 := Vec.elems_eq_to_sound h4
  replace h3 := Vec.seq_sound h3
  replace h5 := Vec.seq_sound h5
  replace h6 := Vec.seq_sound h6
  replace h8 := Vec.seq_sound h8
  replace h9 := Vec.seq_sound h9
  replace h10 := Vec.get_elem_if_eq_sound h10;
  apply Typing.mtch
  apply ih1 h1
  apply valid_data_type_sound h2
  apply ih4 h11
  · intro i; replace h4 := h4 i; replace h3 := h3 i
    simp [ValidHeadVariable]; exists (pat_sp i).1;
    constructor
    exists (pat_sp i).2
    assumption
  · intro i; replace h6 := h6 i; apply ih3 i h6
  · intro i; replace h8 := h8 i; apply Ty.stable_type_match_sound h8
  · intro i; replace h5 := h5 i; apply ih2 i h5
  · intro i; replace h9 := h9 i; rw[h10 i] at h9; apply Ty.prefix_type_match_sound h9

case _ Δ _ _ _ _ ih1 ih2 ih3 => -- guard
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h9, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h10, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h11, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h12, h⟩
  cases h
  replace ih1 := ih1 h1; clear h1
  replace ih2 := ih2 h2; clear h2
  replace ih3 := ih3 h9; clear h9
  replace h3 := infer_kind_sound h3
  replace h4 := Kind.is_open_kind_sound h4
  replace h5 := Ty.stable_type_match_sound (Δ := Δ) h5
  replace h6 := valid_open_type_sound h6
  replace h8 := valid_inst_type_sound h8
  replace h10 := Ty.prefix_type_match_sound h10
  apply Typing.guard
  assumption
  assumption
  assumption
  assumption
  assumption
  assumption
  assumption

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
  apply Typing.lam; assumption; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  simp at h; rcases h with ⟨h6, h⟩; rcases h6 with ⟨h6, h7⟩
  subst h; subst h6; subst h7
  replace ih1 := ih1 h1; clear h1
  replace ih2 := ih2 h3; clear h3
  replace h2 := Ty.is_arrow_some_sound h2
  replace h4 := infer_kind_sound h4 wf
  replace h5 := base_kind_some h5
  subst h2; subst h5
  apply Typing.app
  assumption
  assumption
  assumption

case _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  cases h
  replace ih := ih h1
  apply Typing.lamt
  assumption

case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  simp at h; cases h.1; cases h.2
  replace ih1 := ih1 h2; clear h2
  replace h1 := infer_kind_sound h1 wf
  replace h3 := Ty.is_all_some_sound h3
  subst h3
  apply Typing.appt
  assumption
  assumption
  rfl

case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  simp at h; cases h.1.1; cases h.1.2; cases h.2; clear h
  replace ih1 := ih1 h1
  replace ih2 := ih2 h2
  replace h3 := infer_kind_sound h3
  replace h4 := Ty.is_eq_some_sound h4
  subst h4
  apply Typing.cast
  assumption
  assumption

case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  cases h
  replace h1 := infer_kind_sound h1 wf
  apply Typing.refl
  assumption

case _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  cases h
  replace ih := ih h1
  replace h2 := infer_kind_sound h2
  replace h3 := Ty.is_eq_some_sound h3
  subst h3
  apply Typing.sym
  assumption

case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  simp at h; rcases h with ⟨h, e2⟩; subst e2
  rcases h with ⟨e1, e2⟩
  replace ih1 := ih1 h1; clear h1
  replace ih2 := ih2 h4; clear h4
  replace h2 := infer_kind_sound h2 wf
  replace h3 := Ty.is_eq_some_sound h3
  replace h5 := infer_kind_sound h5 wf
  replace h6 := Ty.is_eq_some_sound h6
  subst h3; subst h6
  rw[<-e1] at h5; rw[<-e1] at ih2
  rw[e2] at ih1; rw[e2] at h2
  apply Typing.seq
  assumption
  assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h7, h⟩
  simp at h; rcases h with ⟨e1, e2⟩; subst e2
  replace ih1 := ih1 h1; clear h1
  replace ih2 := ih2 h4; clear h4
  replace h2 := infer_kind_sound h2 wf
  replace h3 := Ty.is_eq_some_sound h3
  replace h5 := infer_kind_sound h5 wf
  replace h6 := Ty.is_eq_some_sound h6
  replace h7 := Kind.is_arrow_sound h7
  subst h3; subst h6
  rw[<-e1] at h7; rw[h7] at ih1; rw[h7] at h2
  apply Typing.appc
  assumption
  assumption

case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h9, h⟩
  cases h;
  replace ih1 := ih1 h1; clear h1
  replace ih2 := ih2 h5; clear h5
  replace h2 := infer_kind_sound h2 wf
  replace h3 := Ty.is_eq_some_sound h3
  replace h4 := Kind.base_kind_sound h4
  replace h6 := infer_kind_sound h6 wf
  replace h7 := Ty.is_eq_some_sound h7
  replace h8 := Kind.base_kind_sound h8
  replace h9 := Kind.is_closed_kind_sound h9
  subst h3; subst h7;
  rw[h4] at ih1; rw[h4] at h2
  rw[h9] at ih2; rw[h9] at h6
  rw[h9] at h8; cases h8
  apply Typing.arrowc
  assumption
  assumption

case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h9, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h10, h⟩
  simp at h; rcases h with ⟨h, e⟩; subst e
  rcases h with ⟨h, e1⟩
  rcases h with ⟨h, e2⟩
  rcases h with ⟨h, e3⟩
  rcases h with ⟨e4, e5⟩
  subst e4; subst e3
  replace ih1 := ih1 h1; clear h1
  replace h2 := Ty.is_eq_some_sound h2
  replace h3 := Ty.is_app_some_sound h3
  replace h4 := Ty.is_app_some_sound h4
  replace h5 := infer_kind_sound h5 wf
  replace h6 := infer_kind_sound h6 wf
  replace h7 := infer_kind_sound h7 wf
  replace h8 := infer_kind_sound h8 wf
  replace h9 := Kind.is_arrow_sound h9
  replace h10 := Kind.is_arrow_sound h10
  rw[e1] at e2;  rw[e1]
  rw[e2]
  rw[e5] at h7; rw[e5] at h8
  subst h2; subst h9; subst h10
  rw[h3] at ih1; rw [h4] at ih1
  simp_all
  apply Typing.fst
  apply h7
  apply h8
  assumption

case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h9, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h10, h⟩
  simp at h; rcases h with ⟨h, e⟩; subst e
  rcases h with ⟨h, e1⟩
  rcases h with ⟨h, e2⟩
  rcases h with ⟨h, e3⟩
  rcases h with ⟨e4, e5⟩
  subst e4; subst e3
  replace ih1 := ih1 h1; clear h1
  replace h2 := Ty.is_eq_some_sound h2
  replace h3 := Ty.is_app_some_sound h3
  replace h4 := Ty.is_app_some_sound h4
  replace h5 := infer_kind_sound h5 wf
  replace h6 := infer_kind_sound h6 wf
  replace h7 := infer_kind_sound h7 wf
  replace h8 := infer_kind_sound h8 wf
  replace h9 := Kind.is_arrow_sound h9
  replace h10 := Kind.is_arrow_sound h10
  rw[e1] at e2;
  rw[e5] at h7; rw[e5] at h8
  subst h2; subst h9; subst h10
  rw[h3] at ih1; rw [h4] at ih1
  simp_all
  apply Typing.snd
  assumption
  assumption
  assumption
case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  cases h
  replace ih1 := ih1 h1; clear h1
  replace h2 := Ty.is_eq_some_sound h2
  replace h3 := Kind.is_closed_kind_sound h3
  rw[h3] at h2; rw[h3]
  subst h2
  apply Typing.allc
  assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  simp at h; rcases h with ⟨h, e⟩; subst e
  rcases h with ⟨h, e1⟩; rcases h with ⟨e2, e3⟩
  replace ih1 := ih1 h1; clear h1
  replace h2 := Ty.is_eq_some_sound h2
  replace h3 := Ty.is_all_some_sound h3
  replace h4 := Ty.is_all_some_sound h4
  replace h5 := ih2 h5
  replace h6 := Ty.is_eq_some_sound h6
  subst h2; subst h6
  rw[e1] at ih1; rw[e2] at h3;  rw[e2] at e3
  rw[h3] at ih1; rw[h4] at ih1
  rw[e3] at h5
  apply Typing.apptc
  assumption
  assumption
  rfl
  rfl
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace ih1 := ih1 h1
  replace ih2 := ih2 h2
  replace h3 := infer_kind_sound h3 wf
  apply Typing.choice
  assumption
  assumption
  assumption
