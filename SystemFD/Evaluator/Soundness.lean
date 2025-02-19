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
  generalize ip : instance_indices' Γ 0 n [] = i at *;
  generalize instsp : get_instances Γ i = insts at *;
  have nfh := @var_neutral_form n; symm at nfh;
  symm at instsp; symm at ip;
  apply Red.inst nfh _ ip instsp; unfold Term.apply_spine; simp_all;
  unfold Term.is_openmethod; rw[om]
case _ Γ n lt et => simp_all
case _ et => simp at et; subst et; apply Red.beta
case _ et => simp at et; subst et; apply Red.betat
case _ et => simp at et; subst et; apply Red.letterm;

case _ Γ f t _ n sp _ t' om et =>
  simp at et; split at et;
  case _ fnf =>
    simp_all;
    generalize ip : instance_indices' Γ 0 n [] = ιs at *;
    generalize instsp : get_instances Γ ιs = insts at *;
    have ftnf := @neutral_form_app f t n sp fnf; symm at ftnf;
    have omp := Term.id_is_openmethod om; symm at ip; symm at instsp
    symm at et; symm at fnf;
    generalize tlp' : List.map (·.apply_spine sp) insts = tl' at *; symm at tlp'
    have fred := Red.inst fnf omp ip instsp tlp';
    apply Red.app_congr fred; simp_all
  case _ =>
    rw[Option.bind_eq_some] at et;
    cases et; case _ w h =>
    have hl := And.left h
    injection (And.right h) with ts; subst ts;
    apply @Red.app_congr Γ f w; simp_all; rfl
case _ Γ t n sp fnf A t' lt et =>
  simp at et; split at et;
  case _ fnf =>
     simp_all;
     have ftnf := @neutral_form_appt f t n sp fnf;
     have omp := Term.id_is_letterm lt; symm at et; symm at lt; symm at fnf;
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
  generalize ip : instance_indices' Γ 0 n [] = ιs at *;
  generalize instsp : get_instances Γ ιs = insts at *;
  simp_all;
  have ftnf := @neutral_form_app f t n sp fnf;
  have omp := Term.id_is_openmethod om; symm at ip; symm at instsp;
  symm at et; symm at fnf;
  generalize tlp' : List.map (·.apply_spine sp) insts = tl' at *; symm at tlp'
  have fred := Red.inst fnf omp ip instsp tlp';
  apply Red.appt_congr fred; simp_all

case _ Γ f t _ n sp fnf A t' lt et =>
  simp at et;
  simp_all;
  have ftnf := @neutral_form_appt f t n sp fnf;
  have omp := Term.id_is_letterm lt; symm at et; symm at lt; symm at fnf;
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
      injection (And.right h) with ts; subst ts;
      apply Red.ite_congr (@ih w (And.left h)); trivial
    case _ =>
    simp_all; split at site;
    case _ =>
      simp_all; rw[Option.bind_eq_some] at site;
      cases site; case _ w h =>
        injection (And.right h) with ts; subst ts;
        apply Red.ite_congr (@ih w (And.left h)); trivial
    case _ sp' sne _ _ =>
     simp at site; split at site;
     case _ =>
       simp_all; rw[Option.bind_eq_some] at site;
       cases site; case _ w h =>
       injection (And.right h) with ts; subst ts;
       apply Red.ite_congr (@ih w (And.left h)); trivial
     case _ =>
       simp at site; split at site;
       case _ ctor =>
         simp at site; split at site;
         case _  _ _ _ _ _ weqs =>
           subst weqs; simp_all; split at site;
           case _ px =>
             injection site with br; rw[<-br]; symm at pne; symm at sne; symm at px;
             apply Red.ite_matched pne sne px; apply Term.id_is_ctor ctor
           case _ npx =>
             injection site with site; subst site; symm at sne; symm at pne;
             have _ :=  option_neg npx;
             apply Red.ite_missed pne sne; simp_all
         case _ cond =>
           symm at pne; symm at sne;
           injection site with ss ; subst ss;
           simp_all; apply Red.ite_missed pne sne; simp_all;
       case _ => simp at site

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
    have ih' := @ih s' (And.left smatch'); simp_all
    have h' := And.right smatch'; subst h'; apply Red.guard_congr ih'; rfl
  case _ s' sp' heq =>
    split at smatch;
    case _ frame_term =>
      simp_all; rw[Option.bind_eq_some] at smatch;
      symm at heq; symm at frame_term; simp_all
      cases smatch;
      case _ w ts' =>
        have ih' := @ih w (And.left ts'); simp_all
        have h' := And.right ts'; subst h'; apply Red.guard_congr ih'; rfl
    case _ =>
      simp_all; split at smatch;
      case _ =>
        simp_all; rw[Option.bind_eq_some] at smatch; cases smatch;
        case _ w ts' =>
        have ih' := @ih w (And.left ts'); simp_all
        have h' := And.right ts'; subst h'; apply Red.guard_congr ih'; rfl
      case _ =>
        simp_all; split at smatch;
        case _ heq' => -- guard_matched
             split at smatch;
             case _ _ _ sl =>
               injection smatch with smatch'; rw[<-smatch'];
               symm at pne; symm at heq; symm at sl; rw [<-heq'] at heq;
               apply Red.guard_matched pne heq sl
             case _ x =>
               symm at pne; symm at heq;
               injection smatch with empt; subst empt
               have temp := option_neg x;
               simp_all; apply Red.guard_missed pne heq;
               simp_all;
        case _ c => -- guard_missed
          simp_all; subst smatch; symm at pne; symm at heq;
          apply Red.guard_missed pne heq;
          simp_all;

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
case _ Γ t t' t'' teq et =>
  have eq := eq_of_beq teq; subst eq;
  simp at et; rw[<-et]; exact Red.appc
case _ Γ t t' t'' teq et =>
  simp at et; have nh := And.left et; contradiction

case _ et => simp at et; subst et; apply Red.fst
case _ et => simp at et; subst et; apply Red.snd
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

case _ Γ t a ih =>
  simp at ih; rw[<-ih]; exact Red.cast
case _ Γ t η x ih1 ih=>
  simp at ih; rw[Option.bind_eq_some] at ih;
  cases ih; case _ h w =>
    have h' := And.right w; injection h' with w';
    have qq := @ih1 h (And.left w)
    rw [<-w']; apply Red.cast_congr qq; rfl
case _ _ et =>  simp at et
