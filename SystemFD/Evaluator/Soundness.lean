import SystemFD.Term
import SystemFD.Reduction
import SystemFD.Ctx
import SystemFD.Evaluator
import SystemFD.Judgment
set_option maxHeartbeats 500000

theorem eval_inst_soundess : eval_inst Γ t = .some ts -> Red Γ t ts := by
intros
induction Γ, t using eval_inst.induct generalizing ts
case _ Γ n _ om et =>
  simp_all; subst et;
  generalize instsp : get_instances Γ n = insts at *;
  have nfh := @Term.var_neutral_form n; symm at nfh;
  symm at instsp;
  apply Red.inst nfh _ instsp; unfold Term.apply_spine; simp_all;
  unfold Ctx.is_openm; rw[om]; unfold Frame.is_openm; simp_all;
case _ Γ n _ _ lt et =>
    simp at et; rw [lt] at et; simp at et; subst et;
    have nf :=  @Term.var_neutral_form n; symm at nf; symm at lt;
    apply Red.letterm nf lt;
case _ et => simp at et
case _ et => simp at et; subst et; apply Red.beta
case _ et => simp at et; subst et; apply Red.betat
case _ Γ _ _ _ et => simp at et; subst et; apply Red.letbeta

case _ Γ f t _ n sp _ t' om et =>
  simp at et; split at et;
  case _ fnf =>
    simp_all;
    generalize instsp : get_instances Γ n = insts at *;
    have ftnf := @Term.neutral_form_app f t n sp fnf; symm at ftnf;
    symm at instsp
    symm at et; symm at fnf;
    generalize tlp' : List.map (·.apply_spine sp) insts = tl' at *; symm at tlp'
    have omp : Γ.is_openm n := by unfold Ctx.is_openm; rw[om]; unfold Frame.is_openm; simp
    have fred := Red.inst fnf omp instsp tlp';
    apply Red.app_congr fred; simp_all
  case _ =>
    rw[Option.bind_eq_some] at et;
    cases et; case _ w h =>
    have hl := And.left h
    injection (And.right h) with ts; subst ts;
    apply @Red.app_congr Γ f w; simp_all; rfl
case _ Γ f t _ n sp fnf A t' lt et =>
  simp at et; split at et;
  case _ fnf =>
     simp_all;
     have ftnf := @Term.neutral_form_appt f t n sp fnf;
     symm at et; symm at lt; symm at fnf;
     have fred := @Red.letterm A f n sp Γ t' fnf lt;
     rw[et]; apply Red.app_congr fred; simp_all
  case _ => simp_all
case _ et =>
  simp at et; split at et;
  case _ => simp_all
  case _ => simp_all
case _ Γ f t _ nf ih et =>
  simp at et; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts;
    apply Red.app_congr ih'; rfl
case _ Γ f t _ n sp fnf _ om et =>
  simp at et;
  generalize instsp : get_instances Γ n = insts at *;
  simp_all;
  have ftnf := @Term.neutral_form_app f t n sp fnf;
  have omp : Γ.is_openm n := by simp; rw[om]; unfold Frame.is_openm; simp;
  symm at instsp;
  symm at et; symm at fnf;
  generalize tlp' : List.map (·.apply_spine sp) insts = tl' at *; symm at tlp'
  have fred := Red.inst fnf omp instsp tlp';
  apply Red.appt_congr fred; simp_all

case _ Γ f t _ n sp fnf A t' lt et =>
  simp at et;
  simp_all;
  have ftnf := @Term.neutral_form_appt f t n sp fnf;
  symm at et; symm at lt; symm at fnf;
  have fred := @Red.letterm A f n sp Γ t' fnf lt;
  rw[et]; apply Red.appt_congr fred; simp_all

case _ et =>
  simp at et; split at et;
  case _ => simp_all;
  case _ => simp_all;
case _ Γ f t _ nf ih et =>
  simp at et; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts;
    apply Red.appt_congr ih'; rfl

-- ITE
case _ Γ p s b c ih et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
    have pne := And.left h;
    have site := And.right h;
    simp at site; split at site; simp_all;
    case _ =>
      rw[Option.bind_eq_some] at site;
      cases site; case _ w h =>
      cases h; case _ h =>
      injection (And.right h) with ts; subst ts; simp at h;
      apply Red.ite_congr (ih h); simp;
    case _ snf =>
      simp_all;
      have wisctor := site.1;
      replace site := site.2;
      split at site;
      case _ => rw[Option.bind_eq_some] at site; cases site; case _ w h =>
        simp at h;
        have tl' := h.2;
        subst tl';
        apply Red.ite_congr (ih h.1); simp;
      case _ s'_stable =>
        simp_all; split at site;
        case _ headeqs =>
          split at site;
          case _ pfix =>
            injection site with site; subst headeqs;
            symm at snf; symm at pne; subst site; symm at pfix;
            apply Red.ite_matched pne snf pfix wisctor;
          case _ pfix =>
             injection site with site; subst site; symm at snf; symm at pne;
             have x :=  option_lemma pfix;
             apply Red.ite_missed pne snf s'_stable (Or.inr x)
        case _ h =>
          injection site with site; subst site;
          symm at snf; symm at pne;
          apply Red.ite_missed pne snf s'_stable (Or.inl h)

-- GUARD
case _ Γ p s c ih et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have pne := And.left h;
  have smatch := And.right h;
  simp_all; split at smatch;
  case _ =>
    rw[Option.bind_eq_some] at smatch;
    cases smatch; case _ s' smatch' =>
    cases smatch'; case _ smatch' =>
    have ih' := ih (And.left smatch'); simp_all
    have h' := And.right smatch'; subst h'; apply Red.guard_congr ih'; rfl
  case _ s' sp' snf =>
    split at smatch;
    case _ frame_term =>
      rw[Option.bind_eq_some] at smatch;
      symm at snf; symm at frame_term; simp_all
      cases smatch;
      case _ w ts' =>
        cases ts';
        case _ ts' =>
          have ih' := ih (And.left ts'); simp_all
          have h' := And.right ts'; subst h'; apply Red.guard_congr ih'; rfl
    case _ =>
      simp_all; split at smatch;
      case _ s'_stable s_n =>
        subst s_n; have s_is_inst := smatch.1; replace smatch := smatch.2;
        split at smatch;
        case _ pfix =>
             injection smatch with smatch; subst smatch;
             symm at snf; symm at pne; symm at pfix;
             apply Red.guard_matched pne snf pfix;
        case _ pfix =>
             injection smatch with smatch; subst smatch; symm at snf; symm at pne;
             have x :=  option_lemma pfix;
             apply Red.guard_missed pne snf s'_stable (Or.inr x)
      case _ xx heq =>
           have tl' := smatch.2; injection tl' with tl'; subst tl';
           replace smatch := smatch.1;
           symm at pne; symm at snf;
           have reds : Red Γ (.guard p s c) [] := (Red.guard_missed pne snf xx (Or.inl heq));
           apply reds

case _ Γ _ et => simp at et; rw[<-et]; apply Red.sym
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have et' := ih (And.left h); simp_all; rw[<-And.right h];
  apply Red.sym_congr et'; rfl
case _ Γ t t' teq et =>
  have e := eq_of_beq teq; subst e;
  simp at et; rw [<-et]; exact Red.seq
case _ Γ t' t h et =>
  simp at et; have nh := And.left et; exfalso;
  contradiction

case _ Γ _ ih1 ih2 et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih2 et1;
  apply Red.seq_congr2 lem1; simp
case _ Γ _ _  ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.seq_congr1 lem1; simp

case _ Γ t t' et => simp at et; rw [<-et]; apply Red.appc

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.appc_congr2 lem1; simp

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.appc_congr1 lem1; simp

case _ et => simp at et; subst et; apply Red.fst
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.fst_congr lem1; simp

case _ et => simp at et; subst et; apply Red.snd
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.snd_congr lem1; simp

case _ et => simp at et; subst et; apply Red.arrowc
case _ Γ t η _ ih et =>
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
case _ Γ t η _ ih1 et=>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
    have ih := @ih1 w (And.left h);
    injection (And.right h) with w;
    subst w; apply Red.allc_congr ih; rfl

case _ et =>
  simp at et;  subst et; apply Red.apptc

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.apptc_congr1 lem1; simp

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.apptc_congr2 lem1; simp

case _ Γ t a ih =>
  simp at ih; rw[<-ih]; exact Red.cast
case _ Γ t η x ih1 ih=>
  simp at ih; rw[Option.bind_eq_some] at ih;
  cases ih; case _ h w =>
    have h' := And.right w; injection h' with w';
    have qq := @ih1 h (And.left w)
    rw [<-w']; apply Red.cast_congr qq; rfl
case _ _ et =>  simp at et
