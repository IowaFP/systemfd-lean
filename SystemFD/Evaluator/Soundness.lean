import SystemFD.Term
import SystemFD.Reduction
import SystemFD.Ctx
import SystemFD.Evaluator.SmallStep
import SystemFD.Judgment

set_option maxHeartbeats 5000000

theorem eval_inst_soundess : eval_inst Γ t = .some ts -> Red Γ t ts := by
intro et
induction Γ, t using eval_inst.induct generalizing ts
all_goals try (unfold eval_inst at et)
case _ Γ n _ om et =>
  simp_all; subst et;
  generalize instsp : get_instances Γ n = insts at *;
  have nfh := @Term.var_neutral_form n; symm at nfh;
  symm at instsp;
  apply Red.inst nfh _ instsp; unfold Term.apply_spine; simp_all;
  apply instsp; rfl
  simp; rw[om]; unfold Frame.is_openm; simp

case _ Γ n _ _ lt et =>
    simp at et; rw [lt] at et; simp at et; subst et;
    have nf :=  @Term.var_neutral_form n; symm at nf; symm at lt;
    apply Red.letterm nf lt;
case _ et => simp at et
case _ et => simp at et; subst et; apply Red.beta
case _ et => simp at et; subst et; apply Red.betat
case _ Γ _ _ _ et => simp at et; subst et; apply Red.letbeta

case _ Γ f t e n sp fnf t' om et => -- app openm
  simp at et; rw[fnf] at et; simp at et; rw[om] at et; simp at et
  rw[<-et];
  generalize instsp : get_instances Γ n = ιs at et; symm at instsp
  generalize tlp' : List.map (·.apply_spine sp) ιs = tl' at *; symm at tlp'
  apply Red.ctor2_congr1
  simp
  apply Red.inst;
  apply Eq.symm fnf
  simp; unfold Frame.is_openm; rw[om]
  apply instsp;
  apply tlp'
  rfl

case _ Γ f t _ n sp fnf A t' lt et => -- app term
  simp at et; rw[fnf] at et; simp at et; rw[lt] at et; simp at et
  rw[<-et]
  apply Red.ctor2_congr1
  simp
  apply Red.letterm
  apply Eq.symm fnf
  apply Eq.symm lt

case _ et => -- app
  simp at et; split at et;
  case _ => simp_all
  case _ => simp_all

case _ Γ f t _ nf ih et =>
  simp at et; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts; simp at h;
    apply Red.ctor2_congr1;
    simp; assumption

case _ Γ f t _ n sp fnf _ om et => -- appt openm
  simp at et; rw[fnf] at et; simp at et; rw[om] at et; simp at et
  rw[<-et];
  generalize instsp : get_instances Γ n = ιs at et; symm at instsp
  generalize tlp' : List.map (·.apply_spine sp) ιs = tl' at *; symm at tlp'
  apply Red.ctor2_congr1
  simp
  apply Red.inst;
  apply Eq.symm fnf
  simp; unfold Frame.is_openm; rw[om]
  apply instsp;
  apply tlp'
  rfl

case _ Γ f t _ n sp fnf A t' lt et => -- appt term
  simp at et; rw[fnf] at et; simp at et; rw[lt] at et; simp at et
  rw[<-et]
  apply Red.ctor2_congr1
  simp
  apply Red.letterm
  apply Eq.symm fnf
  apply Eq.symm lt

case _ et =>
  simp at et; split at et
  case _ => simp_all
  case _ => simp_all

case _ Γ f t _ nf ih et =>
  simp at et; simp_all;
  rw[Option.bind_eq_some] at et
  cases et; case _ w h =>
    have ih' := @ih w (And.left h)
    injection (And.right h) with ts; subst ts;
    simp at h
    apply Red.ctor2_congr1; simp; assumption

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
      apply Red.ite_congr (ih h)
    case _ snf =>
      simp_all;
      have wisctor := site.1;
      replace site := site.2;
      split at site;
      case _ => rw[Option.bind_eq_some] at site; cases site; case _ w h =>
        simp at h;
        have tl' := h.2;
        subst tl';
        apply Red.ite_congr (ih h.1)
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
    have h' := And.right smatch'; subst h'; apply Red.guard_congr ih'
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
          have h' := And.right ts'; subst h'; apply Red.guard_congr ih'
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
           have reds : Red Γ (.guard p s c) `0 := (Red.guard_missed pne snf xx (Or.inl heq));
           apply reds

case _ Γ _ et => simp at et; rw[<-et]; apply Red.sym

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have et' := ih (And.left h); simp_all; rw[<-And.right h];
  apply Red.ctor1_congr; assumption

case _ Γ K t K' t' teq et =>
  simp at teq
  have e1 := Term.eq_of_beq teq.1; subst e1;
  have e2 := Term.eq_of_beq teq.2; subst e2;
  simp at et; rw [<-et]; exact Red.seq

case _ Γ K t t' K' h et =>
  simp at et; have nh := And.left et; exfalso;
  simp at h;
  have e := h nh.1
  have e' := nh.2; rw[e] at e'
  contradiction

case _ ih1 ih2 et =>
  simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih2 et1;
  apply Red.ctor2_congr2
  simp; assumption

case _ Γ _ _  ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1
  apply Red.ctor2_congr1
  simp; assumption

case _ Γ K1 K t K2 t' e et =>
  simp at et;
  replace et := et.2; rw [<-et];
  replace e := Term.eq_of_beq e; subst e
  apply Red.appc

case _ Γ K1 K t K2 t' e et =>
  simp at et
  have e1 := Term.eq_of_beq et.1
  cases e1; simp at e

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.ctor2_congr2; simp; assumption

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.ctor2_congr1; simp; assumption

case _ et => simp at et; subst et; apply Red.fst

case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.ctor2_congr2; simp; assumption

case _ et => simp at et; subst et; apply Red.snd
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ u et =>
  have et1 := et.1
  replace et := et.2;  injection et with et; subst et
  have lem1 := ih et1;
  apply Red.ctor2_congr2; simp; assumption

case _ et => -- arrowc
 simp at et; subst et; apply Red.arrowc
case _ ih et =>
 simp at et; rw[Option.bind_eq_some] at et;
 cases et; case _ η' h =>
 have ih' := @ih η' h.1;
 injection h.2 with w; subst w
 apply Red.bind2_congr2; simp; assumption
case _ Γ η η' ih ih1 ih2 et =>
 simp at et; rw[Option.bind_eq_some] at et;
 cases et; case _ η1' h =>
 have ih' := @ih2 η1' h.1;
 injection h.2 with w; subst w; simp at h;
 apply Red.bind2_congr1; simp; assumption

case _ et => -- allc
 simp at et; subst et; apply Red.allc
case _ ih et =>
 simp at et; rw[Option.bind_eq_some] at et;
 cases et; case _ η1' h =>
 have ih' := @ih η1' h.1;
 injection h.2 with w; subst w; simp at h;
 apply Red.bind2_congr2; simp; assumption

case _ et => -- apptc
 simp at et; have e1 := Term.eq_of_beq et.1; subst e1;
 replace et := et.2; subst et
 apply Red.apptc
case _ e et =>
 simp at et; have e1 := Term.eq_of_beq et.1; subst e1
 simp at e
case _ ih et =>
 simp at et; rw[Option.bind_eq_some] at et;
 cases et; case _ u et =>
 have et1 := et.1
 replace et := et.2;  injection et with et; subst et
 have lem1 := ih et1;
 apply Red.ctor2_congr1; simp; assumption
case _ ih et =>
 simp at et; rw[Option.bind_eq_some] at et;
 cases et; case _ u et =>
 have et1 := et.1
 replace et := et.2;  injection et with et; subst et
 have lem1 := ih et1;
 apply Red.ctor2_congr2; simp; assumption

case _ Γ t a ih => -- cast
  simp at ih; rw[<-ih]; exact Red.cast
case _ Γ t η x ih1 ih=>
  simp at ih; rw[Option.bind_eq_some] at ih;
  cases ih; case _ h w =>
  have h' := w.2; injection h' with w';
  have qq := @ih1 h w.1
  rw [<-w'];
  apply Red.ctor2_congr2; simp; assumption

case _ et => simp at et -- zero

case _ et => -- choice
  simp at et; subst et; constructor
case _ et =>
 simp at et; subst et; constructor
case _ h ih1 et =>
  simp at et; rw[h] at et; simp at et; rw[<-et]
  have ih' := ih1 h
  apply Red.ctor2_congr1; simp; assumption
case _ h1 _ h2 _ ih et =>
  simp at et; rw[h1] at et; simp at et; rw[h2] at et; simp at et
  rw[<-et]
  have ih' := ih h2
  apply Red.ctor2_congr2; simp; assumption
case _ h1 h2 _ _ et =>
  simp at et; rw[h1] at et; simp at et; rw[h2] at et; simp at et
case _ et => simp at et
