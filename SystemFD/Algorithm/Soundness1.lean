import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

theorem wf_kind_sound : wf_kind t = .some u -> ⊢ Γ -> Γ ⊢ t : .kind := by
intro h wf
induction t using wf_kind.induct
case _ => constructor; apply wf
case _ A B ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ h1 h2 =>
  cases h2; case _ u2 h2 =>
  constructor; apply ih1 h1; apply ih2 h2.1
case _ t h1 h2 =>
  exfalso
  cases t <;> simp at h
  case _ => apply h1 rfl

theorem infer_kind_sound : infer_kind Γ t = .some A -> ⊢ Γ -> Γ ⊢ t : A := by
intro h wf
induction Γ, t using infer_kind.induct generalizing A
case _ Γ x => -- Var
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  simp at h2; rw [Option.bind_eq_some_iff] at h2
  cases h2; case _ u2 h2 =>
    constructor; apply wf
    rw [h2.2] at h1; rw [h1]
case _ Γ A' B ih => -- ∀[A] B
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  simp at h2; rw [Option.bind_eq_some_iff] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  simp at h3; rw [Option.bind_eq_some_iff] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  injection h4 with e; subst e
  have lem1 := wf_kind_sound h1 wf
  have lem2 : ⊢ (.kind A' :: Γ) := by
    constructor; apply lem1; apply wf;
  have lem3 := ih h2 lem2;
  replace h3 := is_type_some h3; subst h3;
  have lem3 := ih h2 lem2;
  apply Judgment.allt lem1 lem3;

case _ Γ A' B ih1 ih2 => -- A -t> B
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some_iff] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some_iff] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some_iff] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  replace h2 := is_type_some h2; subst h2
  injection h5 with e; subst e
  replace h4 := is_type_some h4; subst h4
  have lem1 := ih1 h1 wf
  have lem2 : ⊢ (.empty :: Γ) := by constructor; assumption
  have lem3 := ih2 h3 lem2
  apply Judgment.arrow;
  assumption; assumption;

case _ Γ f a ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some_iff] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some_iff] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
    replace h2 := is_arrowk_some h2
    simp at h4; have lem1 : u2.fst = u3 := Term.eq_of_beq h4.1
    rw [h2] at h1; rw [<-h4.2]; rw [<-lem1] at h3
    constructor; apply ih1 h1 wf
    apply ih2 h3 wf
case _ ih1 ih2 =>
  simp at h; rw [Option.bind_eq_some_iff] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some_iff] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some_iff] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  rw [Option.bind_eq_some_iff] at h4
  cases h4; case _ u4 h4 =>
  cases h4; case _ h4 h5 =>
  rw [Option.bind_eq_some_iff] at h5
  cases h5; case _ u5 h5 =>
  cases h5; case _ h5 h6 =>
  simp at h6;
  simp at h5; have e := h6.2; subst e
  replace h1 := ih1 h1 wf;
  replace h3 := ih2 h3 wf;
  replace h7 := Term.eq_of_beq h6.1.1; subst h7;
  replace h8 := Term.eq_of_beq h6.1.2; subst h8;
  have h6 := wf_kind_sound h2 wf;
  apply Judgment.eq h6 h1 h3;
case _ Γ t h1 h2 h3 h4 h5 =>
  exfalso
  cases t <;> simp at *
