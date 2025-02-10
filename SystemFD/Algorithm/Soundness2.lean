import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Algorithm.Soundness1

theorem infer_type_sound : infer_type Γ t = .some A -> ⊢ Γ -> Γ ⊢ t : A := by
intro h wf
induction Γ, t using infer_type.induct generalizing A <;> simp at *
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
    replace h1 := wf_kind_sound h1 wf
    constructor; apply h1
    apply ih h2; constructor
    apply h1; apply wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4; cases h4; case _ h4 h5 =>
    subst h5; replace h2 := is_pointed_some h2; subst h2
    have lem := infer_kind_sound h1 wf
    constructor; apply lem; apply h4
    apply ih h3; constructor; apply lem; apply wf
    apply h4
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
    have lem := wf_kind_sound h1 wf
    constructor; apply lem
    apply ih h2; constructor
    apply lem; apply wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    replace h2 := is_const_some h2; subst h2
    replace h1 := infer_kind_sound h1 wf
    constructor; apply h1; apply ih h3
    constructor; apply h1; apply wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    replace h2 := is_const_some h2; subst h2
    replace h1 := infer_kind_sound h1 wf
    constructor; apply h1; apply ih h3
    constructor; apply h1; apply wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4; cases h4; case _ h4 h5 =>
    replace h4 := Term.eq_of_beq h4; subst h4; subst h5
    replace h1 := is_openm_some h1
    constructor; rw [h1]; apply ih1 h2 wf
    apply ih2 h3; constructor; rw [h1]
    apply ih1 h2 wf; apply wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  simp at h5; cases h5; case _ h5 h6 =>
    replace h5 := Term.eq_of_beq h5; subst h5; subst h6
    replace h2 := is_const_some h2; subst h2
    replace h1 := infer_kind_sound h1 wf
    constructor; apply h1; apply ih1 h3 wf
    apply ih2 h4; constructor; apply h1
    apply ih1 h3 wf; apply wf
case _ => constructor; apply wf; rw [h]
case _ Γ p s i e ih1 ih2 ih3 ih4 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  rw [Option.bind_eq_some] at h5
  cases h5; case _ u5 h5 =>
  cases h5; case _ h5 h6 =>
  rw [Option.bind_eq_some] at h6
  cases h6; case _ u6 h6 =>
  cases h6; case _ h6 h7 =>
  rw [Option.bind_eq_some] at h7
  cases h7; case _ u7 h7 =>
  cases h7; case _ h7 h8 =>
  rw [Option.bind_eq_some] at h8
  cases h8; case _ u8 h8 =>
  cases h8; case _ h8 h9 =>
  generalize zdef :
    infer_kind Γ ([P' (List.length u1.to_telescope.fst)]Term.from_telescope_rev u8.reverse u7.to_telescope.snd) = z
    at h9
  rw [Option.bind_eq_some] at h9
  cases h9; case _ u9 h9 =>
  cases h9; case _ h9 h10 =>
  rw [Option.bind_eq_some] at h10
  cases h10; case _ u10 h10 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h11
  cases h11; case _ u11 h11 =>
  cases h11; case _ h11 h12 =>
  simp at h12; cases h12; case _ h12 h13 =>
  cases h12; case _ h12 h14 =>
  cases h12; case _ h12 h15 =>
    sorry
case _ Γ p s t ih1 ih2 ih3 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  rw [Option.bind_eq_some] at h5
  cases h5; case _ u5 h5 =>
  cases h5; case _ h5 h6 =>
  rw [Option.bind_eq_some] at h6
  cases h6; case _ ξ h6 =>
  cases h6; case _ h6 h7 =>
  rw [Option.bind_eq_some] at h7
  cases h7; case _ u7 h7 =>
  cases h7; case _ h7 h8 =>
  rw [Option.bind_eq_some] at h8
  cases h8; case _ u8 h8 =>
  cases h8; case _ h8 h9 =>
  simp at h9; cases h9; case _ h9 h10 =>
  cases h9; case _ h9 h11 =>
  cases h9; case _ h9 h12 =>
    replace h3 := is_unpointed_some h3; subst h3
    replace h8 := is_const_some h8; subst h8; subst h10
    replace h9 := Term.eq_of_beq h9; subst h9
    replace h2 := infer_kind_sound h2 wf
    replace h7 := infer_kind_sound h7 wf
    replace h1 := ih1 h1 wf
    replace h4 := ih2 h4 wf
    replace h5 := ih3 h5 wf
    replace h11 := Term.eq_of_beq h11
    replace h12 := Term.eq_of_beq h12
    generalize τdef : u1.to_telescope.fst = τ at *
    generalize sRdef : u1.to_telescope.snd = sR at *
    have lem1 : (τ, sR) = u1.to_telescope := by sorry
    generalize τpdef : u5.to_telescope.fst = τ' at *
    generalize sTdef : u5.to_telescope.snd = sT at *
    have lem3 : (τ', sT) = u5.to_telescope := by sorry
    apply @Judgment.guard Γ p u1 τ sR ([P' (List.length τ)]sR) s t u5 τ' sT ξ (Term.from_telescope ξ sT) _ _
    apply h1; apply lem1; simp; apply h12; apply h2; apply h4; apply h5
    apply lem3; rw [h6]; rfl; simp; apply h11; apply h7
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    replace h2 := is_const_some h2; subst h2
    replace h1 := infer_kind_sound h1 wf
    constructor; apply h1; apply ih h3
    constructor; apply h1; apply wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4; cases h4; case _ h4 h5 =>
    replace h2 := is_arrow_some h2; subst h2
    replace h4 := Term.eq_of_beq h4; subst h4; subst h5
    constructor; apply ih1 h1 wf
    apply ih2 h3 wf; rfl
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    replace h1 := wf_kind_sound h1 wf
    injection h3 with e; subst e
    constructor; apply h1; apply ih h2
    constructor; apply h1; apply wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4; cases h4; case _ h4 h5 =>
    replace h4 := Term.eq_of_beq h4; subst h4; subst h5
    replace h2 := is_all_some h2; subst h2
    replace h3 := infer_kind_sound h3 wf
    constructor; apply ih h1 wf; apply h3; rfl
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  simp at h3; cases h3; case _ h3 h4 =>
  cases h4; case _ h4 h5 =>
    replace h4 := Term.eq_of_beq h4; subst h4; subst h5
    replace h3 := is_eq_some h3; subst h3
    constructor; apply ih1 h1 wf; apply ih2 h2 wf
case _ =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    replace h1 := infer_kind_sound h1 wf
    replace h2 := is_pointed_some h2; subst h2
    injection h3 with e; subst e
    constructor; apply h1
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ h2 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    replace h3 := is_eq_some h3; subst h3
    constructor; apply ih h1 wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  rw [Option.bind_eq_some] at h
  cases h; case _ h1 h2 =>
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  simp at h5; cases h5; case _ h5 h6 =>
    replace h3 := is_eq_some h3; subst h3; subst h6
    replace h4 := is_eq_some h4; subst h4
    replace h5 := Term.eq_of_beq h5
    constructor; apply ih1 h1 wf; rw [h5]
    apply ih2 h2 wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
    injection h5 with e; subst e
    replace h3 := is_eq_some h3; subst h3
    replace h4 := is_eq_some h4; subst h4
    constructor; apply ih1 h1 wf; apply ih2 h2 wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
    injection h5 with e; subst e
    replace h3 := is_eq_some h3; subst h3
    replace h4 := is_eq_some h4; subst h4
    replace h1 := ih1 h1 wf
    constructor; apply h1; apply ih2 h2
    constructor; apply wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
    injection h5 with e; subst e
    replace h2 := is_eq_some h2; subst h2
    replace h3 := is_appk_some h3
    replace h4 := is_appk_some h4
    rw [h3, h4] at h1
    constructor; apply ih h1 wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
    injection h5 with e; subst e
    replace h2 := is_eq_some h2; subst h2
    replace h3 := is_appk_some h3
    replace h4 := is_appk_some h4
    rw [h3, h4] at h1
    constructor; apply ih h1 wf
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    replace h3 := is_eq_some h3; subst h3
    replace h1 := wf_kind_sound h1 wf
    constructor; apply ih h2; constructor
    apply h1; apply wf
case _ ih1 ih2 =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  rw [Option.bind_eq_some] at h5
  cases h5; case _ u5 h5 =>
  cases h5; case _ h5 h6 =>
  rw [Option.bind_eq_some] at h6
  cases h6; case _ u6 h6 =>
  cases h6; case _ h6 h7 =>
  simp at h7; cases h7; case _ h7 h8 =>
    replace h7 := Term.eq_of_beq h7
    replace h6 := is_eq_some h6; subst h6; subst h8
    replace h3 := is_eq_some h3; subst h3
    replace h4 := is_all_some h4
    replace h5 := is_all_some h5
    rw [h4] at h1; rw [h5] at h1; rw [h7] at h1
    constructor; apply ih1 h1 wf; apply ih2 h2 wf

theorem wf_ctx_sound : wf_ctx Γ = .some u -> ⊢ Γ := by
intro h
induction Γ using wf_ctx.induct generalizing u <;> simp at *
case _ => constructor
case _ ih => constructor; apply ih h
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    have lem := ih h3
    replace h2 := is_const_some h2; subst h2
    constructor; apply infer_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
    have lem := ih h2
    constructor; apply wf_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
    have lem := ih h2
    constructor; apply wf_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    simp at h3; have lem := ih h3.2
    replace h2 := is_pointed_some h2; subst h2
    constructor; apply infer_kind_sound h1 lem
    apply lem; apply h3.1
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
    have lem := ih h2
    constructor; apply wf_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    have lem := ih h3
    replace h2 := is_const_some h2; subst h2
    constructor; apply infer_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    have lem := ih h3
    replace h2 := is_const_some h2; subst h2
    constructor; apply infer_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
    simp at h5; replace h4 := ih h4
    replace h5 := Term.eq_of_beq h5; subst h5
    replace h2 := is_const_some h2; subst h2
    constructor; apply infer_kind_sound h1 h4
    apply infer_type_sound h3 h4; apply h4
case _ hx ih =>
  rw [hx] at h; simp at h
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    simp at h3; replace h2 := ih h2
    replace h3 := Term.eq_of_beq h3; subst h3
    constructor; rw [hx]
    apply infer_type_sound h1 h2; apply h2
