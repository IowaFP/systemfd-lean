import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Algorithm.TypeMatch
import SystemFD.Algorithm.Soundness1

theorem infer_type_sound : infer_type Γ t = .some A -> ⊢ Γ -> Γ ⊢ t : A := by
intro h wf
induction Γ, t using infer_type.induct generalizing A <;> simp at *
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    injection h3 with e; subst e
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
    subst h5; replace h2 := is_type_some h2; subst h2
    have lem := infer_kind_sound h1 wf
    constructor; apply lem; apply h4
    apply ih h3; constructor; apply lem; apply wf
    apply h4
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    injection h3 with e; subst e
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
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    replace h2 := is_type_some h2; subst h2
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
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
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
  cases h8; case _ u7' h8 =>
  cases h8; case _ h8 h9 =>
  rw [Option.bind_eq_some] at h9
  cases h9; case _ u8 h9 =>
  cases h9; case _ h9 h10 =>
  rw [Option.bind_eq_some] at h10
  cases h10; case _ u9 h10 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h11
  cases h11; case _ u10 h11 =>
  cases h11; case _ h11 h12 =>
  rw [Option.bind_eq_some] at h12
  cases h12; case _ u11 h12 =>
  cases h12; case _ h12 h13 =>
  simp at h13; cases h13; case _ h13 h14 =>
  cases h13; case _ h13 h15 =>
    replace h1 := ih1 h1 wf
    replace h2 := ih2 h2 wf
    replace h3 := infer_kind_sound h3 wf
    replace h4 := is_type_some h4
    replace h5 := ih3 h5 wf
    replace h6 := stable_type_match_sound h6
    replace h9 := prefix_type_match_sound h9
    replace h10 := infer_kind_sound h10 wf
    replace h11 := is_type_some h11
    replace h12 := ih4 h12 wf
    replace h13 := Term.eq_of_beq h13
    subst h14; subst h4; subst h11; subst h13
    apply Judgment.ite h1 h2 h3 h5 h6 _ _ h15 h9 h10 h12
    apply u7.snd; apply u7'.snd; rw [h7]; rw [h8]
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
  cases h6; case _ u5' h6 =>
  cases h6; case _ h6 h7 =>
  rw [Option.bind_eq_some] at h7
  cases h7; case _ u7 h7 =>
  cases h7; case _ h7 h8 =>
  rw [Option.bind_eq_some] at h8
  cases h8; case _ u8 h8 =>
  cases h8; case _ h8 h9 =>
  rw [Option.bind_eq_some] at h9
  cases h9; case _ u9 h9 =>
  cases h9; case _ h9 h10 =>
    replace h1 := ih1 h1 wf
    replace h2 := ih2 h2 wf
    replace h3 := infer_kind_sound h3 wf
    replace h4 := is_type_some h4
    replace h5 := stable_type_match_sound h5
    replace h6 := ih3 h6 wf
    replace h7 := prefix_type_match_sound h7
    replace h8 := infer_kind_sound h8 wf
    replace h9 := is_type_some h9
    injection h10 with e; subst e; subst h4; subst h9
    apply Judgment.guard h1 h2 h3 h5 h6 h7 h8
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
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
    constructor; apply infer_kind_sound h1 lem; apply lem
case _ ih =>
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
    have lem := ih h3
    replace h2 := is_type_some h2; subst h2
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
    replace h2 := is_type_some h2; subst h2
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
