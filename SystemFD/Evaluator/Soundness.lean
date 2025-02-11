import SystemFD.Term
import SystemFD.Reduction
import SystemFD.Ctx
import SystemFD.Evaluator
import SystemFD.Algorithm
import SystemFD.Judgment

theorem eval_inst_soundess : eval_inst Γ t = .some ts -> Red Γ t ts := by
intros
induction Γ, t using eval_inst.induct generalizing ts
case _ t Γ n sp tne a oa et =>
  have tnf := Term.spine_lemma tne; subst tnf;
  induction sp
  case _ => simp_all; sorry
  case _ => simp_all; sorry
case _ t Γ n sp head A t' f et =>
    have t' := Term.spine_lemma head; subst t'
    symm at f; sorry
    -- induction sp
    --   case _ =>
    --     have t' := Term.spine_lemma head; symm at head;
    --     simp at t'; subst t'; simp at et; rw [f] at et; simp at et; symm at et; subst et;
    --     symm at f; apply Red.letterm head f; rfl
    --   case _ =>
    --     have t' := Term.spine_lemma head; symm at head;
    --     subst t'; rw [f] at et; simp at et; symm at et; subst et;
    --     symm at f; apply Red.letterm head f; rfl

case _ t Γ n sp head no nt et =>
  have t' := Term.spine_lemma head; subst t';
  simp_all;
  sorry
case _ Γ a b f _ et => simp at et; subst et; apply Red.beta
case _ Γ a b et => simp at et; subst et; apply Red.betat
case _ Γ f t _ nf ih et =>
  simp at et; have fnf := Term.neutral_form_app nf; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts;
    apply Red.app_congr ih'; rfl
case _ nf ih et =>
  simp at et; have fnf := Term.neutral_form_appt nf; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts;
    apply Red.appt_congr ih'; rfl

case _ Γ p s b c _ ih et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have pne := And.left h;
  have smatch := And.right h;
  simp at smatch;
  sorry
case _ Γ p s c _ ih et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have pne := And.left h;
  have smatch := And.right h;
  simp_all;
  sorry
case _ Γ _ _ ih => simp at ih; rw[<-ih]; apply Red.sym
case _ ih η =>
  simp at η; rw[Option.bind_eq_some] at η
  cases η; case _ w η' =>
    have ih' := @ih w (And.left η');
    injection (And.right η') with ts'; symm at ts'; subst ts';
    apply Red.sym_congr ih'; rfl

case _ Γ t t' teq nf ih =>
  have e := eq_of_beq teq; subst e;
  simp at ih; rw [<-ih]; exact Red.seq
case _ Γ t' t h x ih =>
  simp at ih; have nh := And.left ih; exfalso;
  contradiction
case _ Γ t t' t'' teq x et=>
  have eq := eq_of_beq teq; subst eq;
  simp at et; rw[<-et]; exact Red.appc
case _ Γ t t' t'' teq x et=>
  simp at et; have nh := And.left et; contradiction

case _ Γ A B _ et => simp at et; subst et; apply Red.fst
case _ _ _ _ _ et => simp at et; subst et; apply Red.snd
case _ et => simp at et; subst et; apply Red.arrowc
case _ Γ t η _ _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ η' h =>
  have ih' := @ih η' (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.arrowc_congr2 ih'; rfl
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ η' h =>
  have ih' := @ih η' (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.arrowc_congr1 ih'; rfl
case _ et => simp at et; subst et; apply Red.allc
case _ Γ t η _ _ ih1 et=>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
    have ih := @ih1 w (And.left h);
    injection (And.right h) with w;
    subst w; apply Red.allc_congr ih; rfl

case _ Γ t a _ ih=>
  simp at ih; rw[<-ih]; exact Red.cast
case _ Γ t η x _ ih1 ih=>
  simp at ih; rw[Option.bind_eq_some] at ih;
  cases ih; case _ h w =>
    have h' := And.right w; injection h' with w';
    have qq := @ih1 h (And.left w)
    rw [<-w']; apply Red.cast_congr qq; rfl
case _ Γ t K _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w
  apply Red.letdata_congr ih'; rfl
case _ Γ A t t' _ ih et  =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w
  apply Red.letterm_congr ih'; rfl
case _ Γ t t' _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.letctor_congr ih'; rfl
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.letopentype_congr ih'; rfl
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.letopen_congr ih'; rfl
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have ih' := @ih w (And.left h);
  injection (And.right h) with w; subst w;
  apply Red.insttype_congr ih'; rfl
case _ tnone _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _  _ _ _ _ _ _ _ _ _ et =>
  simp at et; rw [tnone] at et;
  simp at et
