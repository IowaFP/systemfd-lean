import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

theorem wf_kind_sound : wf_kind t = .some u -> ⊢ Γ -> Γ ⊢ t : .kind := by
intro h wf
induction t using wf_kind.induct
case _ K => constructor; apply wf
case _ A B ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  simp at h; rw [Option.bind_eq_some] at h
  cases h; case _ h1 h2 =>
  cases h2; case _ u2 h2 =>
  constructor; apply ih1 h1; apply ih2 h2.1
case _ t h1 h2 =>
  exfalso
  cases t <;> simp at h
  case _ => apply h1 _ rfl

theorem infer_kind_sound : infer_kind Γ t = .some A -> ⊢ Γ -> Γ ⊢ t : A := by
intro h wf
induction Γ, t using infer_kind.induct generalizing A
case _ Γ x =>
  simp at h; rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  simp at h2; rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
    constructor; apply wf
    rw [h2.2] at h1; rw [h1]
case _ Γ A' B ih =>
  simp at h; rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  simp at h2; rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  simp at h3; rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    injection h4 with e; subst e
    have lem1 := wf_kind_sound h1 wf
    have lem2 : ⊢ (.kind A' :: Γ) := by
      constructor; apply lem1; apply wf
    constructor; apply lem1
    apply ih h2; apply lem2
    apply wf_kind_sound h3 wf
case _ Γ A' B ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some] at h
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
    replace h2 := is_const_some h2; subst h2
    injection h5 with e; subst e
    replace h4 := is_const_some h4; subst h4
    have lem1 := ih1 h1 wf
    have lem2 : ⊢ (.type A' :: Γ) := by
      constructor; apply lem1; apply wf
    constructor; apply ih1 h1 wf
    apply ih2 h3 lem2
case _ Γ f a ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    replace h2 := is_arrowk_some h2
    simp at h4; have lem1 : u2.fst = u3 := Term.eq_of_beq h4.1
    rw [h2] at h1; rw [<-h4.2]; rw [<-lem1] at h3
    constructor; apply ih1 h1 wf
    apply ih2 h3 wf
case _ ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some] at h
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
    replace h2 := is_pointed_some h2; subst h2
    replace h4 := is_pointed_some h4; subst h4
    constructor; apply ih1 h1 wf; apply ih2 h3 wf
case _ Γ t h1 h2 h3 h4 h5 =>
  exfalso
  cases t <;> simp at *
