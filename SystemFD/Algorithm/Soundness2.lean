import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Algorithm.TypeMatch
import SystemFD.Algorithm.Soundness1

theorem infer_type_sound : infer_type Γ t = .some A -> ⊢ Γ -> Γ ⊢ t : A := by
intro h wf
induction Γ, t using infer_type.induct generalizing A <;> simp at *
case _ Γ n => -- var
  symm at h;
  apply Judgment.var wf h;

case _ Γ p s i e ih1 ih2 ih3 ih4 => -- ite
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
  simp at h13;
  have h14 := h13.2;
  replace h1 := ih1 h1 wf
  replace h2 := ih2 h2 wf
  replace h3 := infer_kind_sound h3 wf
  replace h4 := is_type_some h4
  replace h5 := ih3 h5 wf
  symm at h8;
  replace h8' := stable_type_match_sound h7
  replace h9' := prefix_type_match_sound h10
  replace h10 := infer_kind_sound h11 wf
  replace h11 := is_type_some h12
  replace h12 := ih4 h6 wf
  subst h4; subst h11; subst h14; simp at h13;
  have h6' := h13.1.2; unfold Ctx.is_ctor at h6';
  have h7' := h13.2
  replace h13 := h13.1.1;
  replace h13 := Term.eq_of_beq h13; subst h13;
  have h6'' : ValidHeadVariable p Γ.is_ctor := by apply Exists.intro u7' (And.intro h8 h6');
  have h7'' : ValidHeadVariable u2 Γ.is_datatype
    := by apply Exists.intro u8; apply (And.intro (Eq.symm h9) (by unfold Ctx.is_datatype; apply h7'))
  apply Judgment.ite h1 h2 h3 h5 h6'' h7'' h8' h9' h10 h12

case _ Γ p s t ih1 ih2 ih3 => -- guard
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
  rw [Option.bind_eq_some] at h10
  cases h10; case _ u10 h10 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h11
  cases h11; case _ u11 h11 =>
  cases h11; case _ h11 h12 =>
    replace h1 := ih1 h1 wf
    replace h2 := ih2 h2 wf
    replace h8 := ih3 h8 wf
    replace h3 := infer_kind_sound h3 wf
    replace h4 := is_type_some h4; subst h4;
    replace h9' := stable_type_match_sound h5
    replace h10 := infer_kind_sound h10 wf
    replace h11 := is_type_some h11
    replace h7' := prefix_type_match_sound h9
    subst h11; symm at h6; symm at h7;
    simp at h12; have e := h12.2; subst e; simp at h12;
    have h13 := h12.1; replace h12 := h12.2;
    have h6'' : ValidHeadVariable p Γ.is_insttype := by apply Exists.intro u5' (And.intro h6 h13);
    have h7'' : ValidHeadVariable u2 Γ.is_opent := by apply Exists.intro u7 (And.intro h7 h12);
    apply Judgment.guard h1 h2 h3 h8 h6'' h7'' h9' h7' h10;

case _ ih => -- lam
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
  rw [Option.bind_eq_some] at h4
  cases h4; case _ u7 h7 =>
  cases h7; case _ h7 h8 =>
  rw [Option.bind_eq_some] at h8
  cases h8; case _ u8 h8 =>
  cases h8; case _ h8 h9 =>
  rw [Option.bind_eq_some] at h9
  cases h9; case _ u9 h9 =>
  cases h9; case _ h9 h10 =>
  rw [Option.bind_eq_some] at h10
  cases h10; case _ u10 h10 =>
  cases h10; case _ h10 h11 =>
  injection h6 with h6; subst h6;
  injection h11 with h11; subst h11;
  replace h1 := infer_kind_sound h1 wf;
  replace h2 := is_type_some h2; subst h2;
  replace h3 := ih h3 (Judgment.wftype h1 wf);
  replace h4 := infer_kind_sound h7 wf
  replace h8 := is_type_some h8; subst h8;
  replace h10 := is_type_some h10; subst h10;
  replace h9 := infer_kind_sound h9 (Judgment.wftype h4 wf)
  apply Judgment.lam; assumption; assumption;
  apply Judgment.arrow; assumption; assumption;

case _ ih1 ih2 => -- app
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4; have e := h4.2; subst e; simp at h4;
  replace h2 := is_arrow_some h2; subst h2
  replace h4 := Term.eq_of_beq h4; subst h4;
  replace h1 := ih1 h1 wf;
  replace h4 := ih2 h3 wf;
  apply Judgment.app h1 h4;
  rfl

case _ ih => -- Λ[A]b
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
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u6 h3 =>
  cases h3; case _ h6 h7 =>
  rw [Option.bind_eq_some] at h7
  cases h7; case _ u7 h7 =>
  cases h7; case _ h7 h8 =>
  rw [Option.bind_eq_some] at h8
  cases h8; case _ u8 h8 =>
  cases h8; case _ h8 h9 =>
  injection h9 with e; subst e
  injection h4 with e; subst e
  injection h5 with e; subst e
  replace h1 := wf_kind_sound h1 wf
  replace h2 := ih h2 (Judgment.wfkind h1 wf)
  replace h6 := wf_kind_sound h6 wf;
  replace h7 := infer_kind_sound h7 (Judgment.wfkind h1 wf)
  replace h8 := is_type_some h8; subst h8;
  apply Judgment.lamt; assumption; assumption;
  apply Judgment.allt; assumption; assumption

case _ ih => -- appt
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h4;
  have h5 := h4.2
  replace h4 := h4.1
  replace h4 := Term.eq_of_beq h4; subst h4; subst h5
  replace h2 := is_all_some h2; subst h2
  replace h3 := infer_kind_sound h3 wf
  constructor; apply ih h1 wf; apply h3; rfl

case _ ih1 ih2 => -- cast
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
  replace h3 := is_eq_some h3; subst h3;
  replace h4 := Term.eq_of_beq h4; subst h4; subst h5
  have lem1 := ih1 h1 wf;
  have lem2 := ih2 h2 wf;
  apply Judgment.cast lem1 lem2;

case _ h => -- refl
  rw [Option.bind_eq_some] at h
  cases h; case _ w h =>
  cases h; case _ h1 h2 =>
  replace h1 := infer_kind_sound h1 wf;
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u1 h2 =>
  cases h2; case _ h2 h3 =>
  injection h3 with h3; subst h3;
  replace h2 := wf_kind_sound h2 wf
  apply Judgment.refl h2 h1

case _ ih1 => -- sym
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  injection h3 with e; subst e;
  replace h2 := is_eq_some h2; subst h2;
  have lem1 := ih1 h1 wf;
  apply Judgment.sym lem1


case _ ih1 ih2 => -- seq
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
    have lem1 := ih1 h1 wf;
    have lem2 := ih2 h2 wf;
    replace h3 := is_eq_some h3;
    replace h4 := is_eq_some h4;
    replace h5 := Term.eq_of_beq h5;
    subst h6; rw[<-h5] at h4;
    subst h3; subst h4;
    apply Judgment.seq lem1 lem2

case _ ih1 ih2 => -- appc
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
  simp at h4; cases h4; case _ u4 h5 =>
  cases h5; case _ u5 h5 =>
  cases h5; case _ h4 h6 =>
  rw [Option.bind_eq_some] at h6
  cases h6; case _ u6 h6 =>
  cases h6; case _ h6 h7 =>
  rw [Option.bind_eq_some] at h7
  cases h7; case _ u7 h8 =>
  simp at h8; cases h8; case _ u8 h9 =>
  rw [Option.bind_eq_some] at h9;
  cases h9; case _ u9 h9 =>
  cases h9; case _ h9 h10 =>
  rw [Option.bind_eq_some] at h10;
  cases h10; case _ u10 h10 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h11;
  cases h11; case _ u11 h11 =>
  cases h11; case _ h11 h12 =>
  rw [Option.bind_eq_some] at h12;
  cases h12; case _ u12 h12 =>
  cases h12; case _ h12 h13 =>
  simp at h13;
  have e1 := h13.1.1.1.1; replace e1 := Term.eq_of_beq e1;
  have e3 := h13.1.1.1.2; replace e3 := Term.eq_of_beq e3;
  have e2 := h13.1.1.2; replace e2 := Term.eq_of_beq e2;
  have e4 := h13.1.2; replace e4 := Term.eq_of_beq e4;
  replace h13 := h13.2;
  replace h3 := is_eq_some h3;
  replace h4 := is_eq_some h4;
  replace h11 := is_arrowk_some h11;
  replace h12 := is_arrowk_some h12;
  have lem1 := ih1 h1 wf;
  have lem2 := ih2 h2 wf;
  have lem3 := infer_kind_sound h9 wf;
  have lem4 := infer_kind_sound h10 wf;
  subst h3; subst h4; subst h13; subst e2; subst e4;
  subst h11; subst h12;
  replace h6 := infer_kind_sound h6 wf;
  replace h8 := infer_kind_sound u8 wf;
  apply Judgment.appc h6; rw[<-e1] at h8; rw[<-e3] at h8;
  assumption; assumption; assumption; rw[<-e1] at lem4; assumption;
  assumption;

case _ ih1 ih2 => -- arrowc
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
  rw [Option.bind_eq_some] at h9
  cases h9; case _ u9 h9 =>
  cases h9; case _ h9 h10 =>
  rw [Option.bind_eq_some] at h10
  cases h10; case _ u10 h10 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h11
  cases h11; case _ u11 h11 =>
  cases h11; case _ h11 h12 =>
  rw [Option.bind_eq_some] at h12
  cases h12; case _ u12 h12 =>
  cases h12; case _ h12 h13 =>
  injection h13 with h13
  replace h1 := ih1 h1 wf
  replace h2 := ih2 h2 (Judgment.wfempty wf)
  replace h3 := is_eq_some h3
  replace h4 := infer_kind_sound h4 wf
  replace h5 := is_type_some h5
  replace h6 := infer_kind_sound h6 wf
  replace h7 := is_type_some h7
  replace h8 := is_eq_some h8
  replace h10 := is_type_some h10
  replace h12 := is_type_some h12
  subst h13; subst h5; subst h7; subst h10
  subst h3; subst h8; subst h12
  replace h9 := infer_kind_sound h9 (Judgment.wftype h4 wf)
  replace h11 := infer_kind_sound h11 (Judgment.wftype h6 wf)
  apply Judgment.arrowc;
  assumption; assumption; assumption;assumption; assumption; assumption

case _ ih => -- fst
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
  simp at h9;
  have e1 := h9.2
  have e2 := Term.eq_of_beq h9.1.2
  have e3 := Term.eq_of_beq h9.1.1
  replace h1 := ih h1 wf
  replace h2 := is_eq_some h2
  replace h3 := is_appk_some h3
  replace h4 := infer_kind_sound h4 wf
  replace h5 := is_arrowk_some h5
  replace h6 := is_appk_some h6
  replace h7 := infer_kind_sound h7 wf
  replace h8 := is_arrowk_some h8
  subst h2; subst h8; subst h5;
  subst e1; simp at h9;
  rw [<-e2] at h7; rw [<-e3] at h7;
  rw [h3] at h1; rw [h6] at h1;
  apply Judgment.fst h4 h7 h1;

case _ ih1 ih2 =>  -- let
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
  simp at h7; cases h7; case _ u7 h7 =>
  cases u7; case _ u7 u8 =>
  replace u7 := Term.eq_of_beq u7
  replace h1 := infer_kind_sound h1 wf;
  replace h2 := is_type_some h2; subst h2;
  replace h3 := ih1 h3 wf
  replace h5 := infer_kind_sound h5 wf;
  replace h6 := is_type_some h6; subst h6
  subst h7; subst u7;
  have wf' := Judgment.wfterm h1 h3 wf
  replace h4 := ih2 h4 wf'
  apply Judgment.letterm; assumption; assumption
  replace u8 := Term.eq_of_beq u8;
  rw[u8]; simp; rw [<-u8]; assumption;
  assumption

case _ ih1 => -- snd
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
  simp at h8;
  have e1 := h8.2
  have e2 := Term.eq_of_beq h8.1
  replace h1 := ih1 h1 wf
  replace h2 := is_eq_some h2
  replace h3 := is_appk_some h3
  replace h4 := infer_kind_sound h4 wf
  replace h5 := wf_kind_sound h5 wf
  replace h6 := is_appk_some h6
  replace h7 := infer_kind_sound h7 wf
  subst h2; subst e1; subst e2;
  rw [h3] at h1; rw [h6] at h1;
  apply Judgment.snd h5 h4 h7 h1;

case _ ih => -- ∀c[K]t
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h4 =>
  simp at h4; cases h4; case _ h4 h5 =>
  rw [Option.bind_eq_some] at h4;
  cases h4; case _ u4 h4 =>
  have h6 := h4.1;
  replace h4 := h4.2;
  rw [Option.bind_eq_some] at h4;
  cases h4; case _ u5 h4 =>
  have h7 := h4.1;
  replace h4 := h4.2;
  rw [Option.bind_eq_some] at h4;
  cases h4; case _ u6 h4 =>
  have e := h4.2;
  replace h4 := h4.1;
  rw [Option.bind_eq_some] at h5;
  cases h5; case _ u8 h8 =>
  have h9 := h8.2;  replace h8 := h8.1;
  rw [Option.bind_eq_some] at h9;
  cases h9; case _ u9 h9 =>
  rw [Option.bind_eq_some] at h9;
  cases h9; case _ h10 h9 =>
  cases h10; case _ h10 h11 =>
  rw [Option.bind_eq_some] at h9;
  cases h9; case _ u11 h13 =>
  cases h13; case _ h13 h14 =>
  rw [Option.bind_eq_some] at h11;
  cases h11; case _ u12 h11 =>
  cases h11; case _ h15 h11 =>
  cases h11; case _ u13 h16 =>
  rw [Option.bind_eq_some] at h16;
  cases h16; case _ u16 h16 =>
  cases h16; case _ h16 h17 =>
  injection h17 with h17; subst h17;
  injection e with e; subst e;
  replace h6 := wf_kind_sound h6 wf;
  have wf' := Judgment.wfkind h6 wf
  have lem1 := ih h1 wf'
  replace h2 := is_eq_some h2; subst h2;
  replace h7 := infer_kind_sound h7 wf'
  replace h4 := is_type_some h4; subst h4
  replace u13 := infer_kind_sound u13 wf'
  replace h16 := is_type_some h16; subst h16
  injection h14 with h14; subst h14
  apply Judgment.allc;
  apply Judgment.allt; assumption; assumption;
  apply Judgment.allt; assumption; assumption; assumption

case _ ih1 ih2 => -- appc
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
  simp at h9;
  have e1 := h9.2
  have e2 := Term.eq_of_beq h9.1.2
  have e3 := Term.eq_of_beq h9.1.1.2
  have e4 := Term.eq_of_beq h9.1.1.1
  replace h3 := is_eq_some h3
  replace h6 := is_eq_some h6
  replace h4 := is_all_some h4
  replace h5 := is_all_some h5
  have lem1 := ih1 h1 wf;
  have lem2 := ih2 h2 wf;
  replace h7 := infer_kind_sound h7 wf
  replace h8 := infer_kind_sound h8 wf
  rw[e4] at h4;
  subst h3; subst h6;
  subst e1; subst e2; subst e3; simp at h9
  apply Judgment.apptc;
  rw[h4] at lem1; rw[h5] at lem1;
  assumption; rw[e4] at h7; assumption;
  rw[e4] at h8; assumption;
  assumption; rfl; rfl

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

case _ ih => -- wfctor
  rw [Option.bind_eq_some] at h
  cases h; case _ u1 h =>
  cases h; case _ h1 h2 =>
  rw [Option.bind_eq_some] at h2
  cases h2; case _ u2 h2 =>
  cases h2; case _ h2 h3 =>
  rw [Option.bind_eq_some] at h3;
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  simp at h3; have wf := ih h4;
  replace h2 := is_type_some h2; subst h2;
  constructor; apply infer_kind_sound h1 wf;
  apply wf; apply valid_ctor_sound h3;
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
  rw [Option.bind_eq_some] at h3
  cases h3; case _ u3 h3 =>
  cases h3; case _ h3 h4 =>
  have lem := ih h4;
  replace h2 := is_type_some h2; subst h2
  constructor; apply infer_kind_sound h1 lem; apply lem;
  apply valid_insttype_sound h3;
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
