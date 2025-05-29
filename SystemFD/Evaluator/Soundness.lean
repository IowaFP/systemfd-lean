import SystemFD.Term
import SystemFD.Term.Equality
import SystemFD.Reduction
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Evaluator.SmallStep

-- set_option maxHeartbeats 5000000


theorem eval_choice_mapping_soudness : eval_choice_mapping Γ t = .some t' -> Red Γ t t' := by
intro et
induction Γ, t using eval_choice_mapping.induct generalizing t'
all_goals (simp at et)
all_goals try (rw[<-et])

case _ => apply Red.ite_map
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ u1 et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.ite_congr; assumption

case _ => apply Red.guard_map
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ u1 et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.guard_congr; assumption

case _ => apply Red.ctor1_map

case _ ih1 ih2 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ u1 et =>
  cases et; case _ h1 et =>
  cases et
  replace h2 := ih2 h1
  apply Red.ctor1_congr; assumption

case _ => apply Red.ctor2_map2; simp; simp

case _ => apply Red.ctor2_map2; simp; simp

case _ => apply Red.ctor2_map2; simp; simp

case _ =>
  simp_all; rw[<-et]; apply Red.ctor2_congr1; simp; assumption

case _ =>
  simp_all; rw[<-et]; apply Red.ctor2_congr2; simp; assumption

case _ h1 h2 _ _ => rw[h1] at et; rw[h2] at et; simp at et

case _ h => simp_all

case _ =>
  simp_all
  cases et; case _ h1 et =>
  cases et; case _ h2 et =>
  apply Red.ctor2_map1;  assumption; assumption

case _ h =>
  cases et; case _ h1 et =>
  cases et; case _ h2 et =>
  simp at h; rw[h] at h2; cases h2

case _ => simp_all; rw[<-et]; apply Red.ctor2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all

case _ => apply Red.bind2_map1; simp
case _ => apply Red.bind2_map2; simp

case _ => simp_all; rw[<-et]; apply Red.bind2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all


theorem eval_const_folding1_soudness : eval_const_folding1 Γ t = .some t' -> Red Γ t t' := by
intro et
induction Γ, t using eval_const_folding1.induct generalizing t'
all_goals(simp at et)
all_goals try (rw[<-et])

case _ => apply Red.ite_absorb
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.ite_congr; assumption

case _ => apply Red.guard_absorb
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.guard_congr; assumption

case _ => apply Red.ctor1_absorb
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.ctor1_congr; assumption

case _ => apply Red.choice1
case _ => apply Red.choice2

case _ => rw[<-et.2]; apply Red.ctor2_absorb1; simp; assumption
case _ => simp_all
case _ => rw[<-et.2]; apply Red.ctor2_absorb2; assumption

case _  h => simp_all

case _ => simp_all; rw[<-et]; apply Red.ctor2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all

case _ => apply @Red.bind2_absorb1 .arrowc; simp
case _ => apply @Red.bind2_absorb2 .allc; simp

case _ => simp_all; rw[<-et]; apply Red.bind2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all


theorem eval_const_folding2_soudness : eval_const_folding2 Γ t = .some t' -> Red Γ t t' := by
intro et
induction Γ, t using eval_const_folding2.induct generalizing t'
all_goals(simp at et)
all_goals try (rw[<-et])

all_goals try (
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.ctor1_congr; assumption
)

case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.ite_congr; assumption

case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.guard_congr; assumption

case _ v _ _ => cases v; apply Red.sym;

case _ => apply Red.cast
case _ => apply Red.fst
case _ => apply Red.snd

case _ h =>
  simp at h;
  have e1 := Term.eq_of_beq h.1
  have e2 := Term.eq_of_beq h.2
  rw[<-et.2]; subst e1; subst e2
  apply Red.seq
case _ h =>
  simp at h
  exfalso; have h' := h et.1.1
  have e := et.1.2; rw[h'] at e; simp at e

case _ h =>
  replace h := Term.eq_of_beq h
  have h1 := Term.eq_of_beq et.1
  cases et; case _ et =>
  cases h1;
  rw[<-et]
  apply Red.appc
case _ h =>
  replace h := Term.eq_of_beq et.1
  have h1 := Term.eq_of_beq et.1
  rw[<-et.2];
  cases h1;
  apply Red.appc

case _ =>
  replace h := Term.eq_of_beq et.1
  have h1 := Term.eq_of_beq et.1
  rw[<-et.2];
  cases h1;
  apply Red.apptc

case _ =>
  have h := Term.eq_of_beq et.1; cases h; simp_all

case _ => simp_all; rw[<-et]; apply Red.ctor2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all

case _ => apply Red.arrowc
case _ => apply Red.allc

case _ => simp_all; rw[<-et]; apply Red.bind2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all



theorem eval_inst_soundess : eval_inst Γ t = .some t' -> Red Γ t t' := by
intro et
induction Γ, t using eval_inst.induct generalizing t'
all_goals (simp at et)
all_goals try (rw[<-et])

all_goals try (
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ et =>
  cases et; case _ h1 et =>
  cases et;
  replace h1 := ih1 h1
  apply Red.ctor1_congr; assumption
)

all_goals try (
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ t' et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.bind2_congr2; simp; assumption
)

all_goals try (
case _ ih1 =>
  rw[Option.bind_eq_some] at et;
  cases et; case _ t' et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.bind2_congr1; simp; assumption
)

case _ Γ n _ om =>
  simp_all; subst et;
  generalize instsp : get_instances Γ n = insts at *;
  have nfh := @Term.var_neutral_form n; symm at nfh;
  symm at instsp;
  apply Red.inst nfh _ instsp; unfold Term.apply_spine; simp_all;
  apply instsp; rfl
  simp; rw[om]; unfold Frame.is_openm; simp
case _ Γ n _ _ lt =>
    rw [lt] at et; simp at et; subst et;
    have nf :=  @Term.var_neutral_form n; symm at nf; symm at lt;
    apply Red.letterm nf lt;
case _ => apply Red.letbeta
case _ Γ p s b c ih =>
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

case _ Γ p s c ih =>
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

case _ => apply Red.beta

case _ n _ tnf ih1 => -- app recursive case
  rw[tnf] at et; simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ t' et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.ctor2_congr1; simp; assumption

case _ Γ f t e n sp fnf t' om => -- app openm
  rw[fnf] at et; simp at et; rw[om] at et; simp at et
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

case _ n _ tnf _ _ lt => -- app let term
  rw[tnf] at et; simp at et;
  rw [lt] at et; simp at et; subst et;
  apply Red.ctor2_congr1; simp;
  symm at tnf; symm at lt;
  apply Red.letterm; assumption; assumption

case _ n _ tnf _ _ => -- app bogus
  rw[tnf] at et; simp at et;


case _ => apply Red.betat

case _ n _ tnf ih1 => -- appt recursive case
  rw[tnf] at et; simp at et;
  rw[Option.bind_eq_some] at et;
  cases et; case _ t' et =>
  cases et; case _ h1 et =>
  cases et
  replace h1 := ih1 h1
  apply Red.ctor2_congr1; simp; assumption

case _ Γ f t e n sp fnf t' om =>  -- appt openm
  rw[fnf] at et; simp at et; rw[om] at et; simp at et
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

case _ n _ tnf _ _ lt => -- appt let term
  rw[tnf] at et; simp at et;
  rw [lt] at et; simp at et; subst et;
  apply Red.ctor2_congr1; simp;
  symm at tnf; symm at lt;
  apply Red.letterm; assumption; assumption

case _ n _ tnf _ _ => -- appt bogus
  rw[tnf] at et; simp at et;

case _ => simp_all; rw[<-et]; apply Red.ctor2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.ctor2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all

case _ => simp_all; rw[<-et]; apply Red.bind2_congr1; assumption; assumption
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all
case _ => simp_all; rw[<-et]; apply Red.bind2_congr2; assumption; assumption
case _ => simp_all
case _ => simp_all


theorem eval_small_step_soundness : eval_small_step Γ t = some t' -> Red Γ t t' := by
intro et; unfold eval_small_step at et
split at et
case _ =>
 cases et; case _ et =>
 apply eval_choice_mapping_soudness et
case _ e =>
  split at et
  case _ =>
    cases et; case _ et =>
    apply eval_const_folding1_soudness et
  case _ =>
    split at et
    case _ =>
      cases et; case _ et =>
      apply eval_const_folding2_soudness et
    case _ =>
      split at et
      case _ =>
        cases et; case _ et =>
        apply eval_inst_soundess et
      cases et
