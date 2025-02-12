import SystemFD.Term
import SystemFD.Reduction
import SystemFD.Ctx
import SystemFD.Evaluator
import SystemFD.Algorithm
import SystemFD.Judgment
set_option maxHeartbeats 500000


theorem unfolding_eval_inst_lemma :
   t.neutral_form = .some (h, sp) ->
   eval_inst Γ t = (match (Γ d@ h) with
                   | .openm _ =>
                       List.map (·.apply_spine sp) (get_instances Γ (instance_indices' Γ 0 h []))
                   | .term _ b => .some [ b.apply_spine sp ]  -- inline a let bound term
                   | _ => .none) := by
intros ih;
sorry

theorem eval_inst_soundess : eval_inst Γ t = .some ts -> Red Γ t ts := by
intros
induction Γ, t using eval_inst.induct generalizing ts
case _ t Γ n sp tne a oa et =>
  have tnf := Term.spine_lemma tne; rw [tnf] at et;
  simp_all; have uf := @unfolding_eval_inst_lemma Γ ((#n).apply_spine sp) n sp tne;
  simp_all; rw[<-et];
  generalize ip : instance_indices' Γ 0 n [] = i at *;
  generalize instsp : get_instances Γ i = insts at *;
  symm at instsp; symm at ip;
  apply Red.inst tne _ ip instsp; rfl; simp_all;
case _ t Γ n sp head A t' f et =>
    have t' := Term.spine_lemma head; subst t'; simp_all;
    symm at f; have uf := @unfolding_eval_inst_lemma Γ ((#n).apply_spine sp) n sp head;
    rw [uf] at et; simp_all; split at et;
    case _ => simp_all
    case _ a b heq => simp_all; symm at heq; rw [<-et]; apply Red.letterm head heq
    case _ => simp_all
case _ t Γ n sp head no nt et =>
  have t' := Term.spine_lemma head; subst t';
  simp_all; have uf := @unfolding_eval_inst_lemma Γ ((#n).apply_spine sp) n sp head;
  rw [uf] at et; simp_all
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

-- ITE
case _ Γ p s b c _ ih et =>
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
        case _ sp' heq _ _ =>
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
              case _  _ _ _ _ _ heq' =>
                simp_all; have ss := And.right site; rw[<-ss]; symm at pne; symm at heq; symm at heq'
                have ss' := And.left site; subst ss'; symm at ctor;
                subst ss; simp_all; apply Red.ite_matched pne heq heq'; unfold Term.is_ctorid;
                rw[<-ctor]
              case _ cond =>
                symm at heq; symm at pne;
                have ss := And.left site; have ss' := And.right site; injection ss' with sss'; subst sss'
                simp_all; apply Red.ite_missed pne heq;
                have tt := option_neg cond; simp_all
            case _ => simp at site

-- GUARD
case _ Γ p s c _ ih et =>
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

case _ Γ _ _ et => simp at et; rw[<-et]; apply Red.sym
case _ ih et =>
  simp at et; rw[Option.bind_eq_some] at et;
  cases et; case _ w h =>
  have et' := ih (And.left h); simp_all; rw[<-And.right h];
  apply Red.sym_congr et'; rfl

case _ Γ t t' teq nf et =>
  have e := eq_of_beq teq; subst e;
  simp at et; rw [<-et]; exact Red.seq
case _ Γ t' t h x et =>
  simp at et; have nh := And.left et; exfalso;
  contradiction
case _ Γ t t' t'' teq _ et =>
  have eq := eq_of_beq teq; subst eq;
  simp at et; rw[<-et]; exact Red.appc
case _ Γ t t' t'' teq x et =>
  simp at et; have nh := And.left et; contradiction

case _ et => simp at et; subst et; apply Red.fst
case _ et => simp at et; subst et; apply Red.snd
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
