
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction

-- inductive Neutral : Ctx Term -> Term -> Prop where
--   | varNe : ¬ Γ.is_stable n
--           -> Neutral Γ (#n)
--   | iteNe : Neutral Γ s -> Neutral Γ (.ite p s b c)
--   | guardNe : Neutral Γ s -> Neutral Γ (.guard p s c)
--   | appNe : Neutral Γ t
--           -> Neutral  Γ  (t `@ t')
--   | apptNe : Neutral Γ t
--            -> Neutral Γ (t `@t t')
--   | castNe : Neutral  Γ η
--            -> Neutral Γ (t ▹ η)
--   | fstNe : Neutral Γ η
--           -> Neutral  Γ (η .!1)
--   | sndNe : Neutral  Γ η
--           -> Neutral Γ (η .!2)
--   | symNe : Neutral  Γ η
--          -> Neutral  Γ (sym! η)
--   | seq1 : Neutral  Γ η
--          -> Neutral  Γ (η `; η')
--   | seq2 : Neutral  Γ η'
--          -> Neutral  Γ (η `; η')

inductive Val : Ctx Term -> Term -> Prop where
  | app : t.neutral_form = .some (n, ts)
        -> (Γ.is_stable_red n)
        -> Val Γ t
  | appk : Val Γ (f `@k a)
  | lam :  Val Γ (`λ[a] b)
  | lamt : Val Γ (Λ[A] b)
  | refl : Val Γ (refl! _)
  | star : Val Γ ★
  | arr :  Val Γ (A -t> B)
  | arrk : Val Γ (A -k> B)
  | all : Val Γ (∀[A]B)
  | eq : Val Γ (A ~ B)


theorem flip_eq : Γ ⊢ (A ~ B) : ★ -> Γ ⊢ (B ~ A) : ★ := by
intros h; cases h; case _ k AJ BJ => apply Judgment.eq k BJ AJ


theorem not_neutral_form_shape : Val Γ t ->
        t.neutral_form = .some (n, ts)
        -> ¬ ((t = `λ[A] b)
            ∨ (t = Λ[A] b)
            ∨ t = .letterm A t' b
            ∨ t = .guard p s b
            ∨ t = .ite p s b c
            ∨ t = .kind
            ∨ t = .type
            -- ∨ t = refl! A
            -- ∨ t = sym! η
            ) := by
intros tnf; induction t;
any_goals (solve | simp_all)

def DeclCtx (Γ : Ctx Term) : Prop := ∀ n, Γ.is_stable_red n
namespace DeclCtx
theorem consempty : DeclCtx Γ -> DeclCtx (.empty :: Γ) := by
  intros dctx; induction Γ
  case _ =>
    unfold DeclCtx; unfold Ctx.is_stable_red; unfold Frame.is_stable_red; simp_all; intro n;
    split;
    any_goals (solve | simp_all)
    case _ h =>
      unfold dnth at h; simp_all; split at h;
      any_goals (solve | simp_all)
      case _ h' => cases h'; cases h
      case _ h' => cases h'; cases h;
    case _ h =>
      unfold dnth at h; simp_all; split at h;
      any_goals (solve | simp_all)
      case _ h' => cases h'; cases h
      case _ h' => cases h'; cases h;
    case _ h =>
      unfold dnth at h; simp_all; split at h;
      any_goals (solve | simp_all)
      case _ h' => cases h'; cases h
      case _ h' => cases h'; cases h;
    case _ h =>
      unfold dnth at h; simp_all; split at h;
      any_goals (solve | simp_all)
      case _ h' => cases h'; cases h; sorry
      case _ h' => sorry
  case _ =>
  sorry
theorem conskind : DeclCtx Γ -> DeclCtx (.kind t :: Γ) := by sorry

end DeclCtx

theorem no_lam_bindings : (DeclCtx Γ) -> ∀ x, ¬  (Γ d@ x = .type T) := by
intro dctx x h;
have xx := dctx x; simp at xx; rw[h] at xx; unfold Frame.is_stable_red at xx; simp_all;

theorem dt_is_dt {Γ : Ctx Term}: Γ d@x = Frame.datatype t -> (Γ d@ x).is_datatype := by
intros dt; simp_all; unfold Frame.is_datatype; simp;

theorem dt_is_stable {Γ : Ctx Term}{x : Nat}: Γ d@ x = Frame.datatype t -> Frame.is_stable_red (Γ d@ x) := by
intros dt; unfold Frame.is_stable_red; rw [dt];

theorem opent_is_stable {Γ : Ctx Term}: Γ d@x = Frame.opent t -> Frame.is_stable_red (Γ d@ x) := by
intros dt; unfold Frame.is_stable_red; rw [dt];

theorem apptneqrefl : ¬ ((f `@t a) = (refl! A)) := by simp_all
theorem appneqrefl : ¬ ((f `@ a) = (refl! A)) := by simp_all

theorem openm_no_stable {Γ : Ctx Term}{n : Nat} :
  Frame.is_openm (Γ d@ n) = true -> ¬ (Frame.is_stable_red (Γ d@ n)) := by
intros om; simp_all; unfold Frame.is_openm at om; split at om;
case _ => unfold Frame.is_stable_red; simp_all;
case _ => simp_all

theorem stable_no_reduce : t.neutral_form = .some (n, sp) -> Γ.is_stable_red n = true -> ¬ ∃ t', Red Γ t t' := by
intros tnf nstable x; cases x;
  case _ w h =>
  simp_all; induction h generalizing n sp;
  any_goals (solve | simp_all)
  case _ Γ _ _ _ _ om _ _ nstable =>
    have n_not_stable := openm_no_stable om;
    simp_all;
  case _ hnf idx =>
    unfold Frame.is_stable_red at nstable; symm at hnf;
    have uniq' := Term.unique_neutral_form hnf tnf; have uniq := uniq'.1;
    subst uniq; rw [<-idx] at nstable; simp_all
  case _ f _ _ a _ _ ih =>
    simp_all; rw[Option.bind_eq_some] at tnf;
    cases tnf; case _ w h =>
      have fa_spine := @Term.neutral_form_app f a w.fst w.snd h.1;
      have f_spine := Term.neutral_form_app_rev fa_spine;
      have xx := @ih w.1 w.2 f_spine; simp at h;
      have wfst := And.left (And.right h); symm at wfst;
      subst wfst; simp_all;
  case _ ih =>
    simp_all; rw [Option.bind_eq_some] at tnf;
    cases tnf; case _ f _ _ a _ _ w h =>
      have fa_spine := @Term.neutral_form_appt f a w.fst w.snd h.1;
      have f_spine := Term.neutral_form_appt_rev fa_spine;
      have xx := @ih w.1 w.2 f_spine; simp at h;
      have wfst := And.left (And.right h); symm at wfst;
      subst wfst; simp_all;

@[simp]
abbrev ValueNoSteps : (v : JudgmentVariant) -> (Γ : Ctx Term)  -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , _) => Val Γ t -> ¬ ∃ t', Red Γ t t'
| .wf  => λ _ => λ () => true


theorem val_no_red :
  ⊢ Γ -> DeclCtx Γ ->
  Judgment v Γ ix ->
  ValueNoSteps v Γ ix
  := by
intros wΓ dctx tJ; induction tJ;
any_goals(solve | simp_all)
all_goals(intro vt treds; cases treds; cases vt; simp_all)
case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ h _ _ =>
  cases h;
  case _  n _ x_stable _ _ _ _ _ x_openm _ _ nnf _ =>
    symm at nnf; have nnf' := @Term.var_neutral_form n; rw[nnf'] at nnf; injection nnf with nnf; simp at nnf;
    have x_n := nnf.1; rw[<-x_n] at x_openm;
    have x_not_stable := Frame.is_openm_implies_not_is_stable_red x_openm; contradiction;
  case _ n' _ x_stable _ _ n _ _ x_term nnf =>
    symm at nnf; have nnf' := @Term.var_neutral_form n'; rw[nnf'] at nnf; simp at nnf;
    have n_n := nnf.1; rw[n_n] at x_stable; rw[<-x_term] at x_stable;
    unfold Frame.is_stable_red at x_stable; simp at x_stable;
case _ h =>
  cases h;
  case _ h _ => cases h
  case _ h => cases h
case _ h =>
  cases h;
  case _ h _ => cases h
  case _ h => cases h
case _ h =>
  cases h
  case _ h _ => cases h
  case _ h => cases h
case _ h =>
  rw [Option.bind_eq_some] at h; cases h
  case _ h _ _ _ =>
    cases h;
    case _ _ x_stable _ _ _ _ _ _ x_openm _ _ hh _ =>
      simp_all; have hh := hh.1; subst hh; simp_all;
      have x_not_stable := Frame.is_openm_implies_not_is_stable_red x_openm; contradiction;
    case _ Γ f _ _ arg _ _ n ts _ _ x_stable w fnfp _ x sp _ x_term hh =>
      have fnf := fnfp.2;
      injection fnf with fnf;
      have weqx : w.fst = n := by simp_all;
      have tseqw :  w.snd ++ [(.kind, arg)]= ts := by simp_all;
      symm at tseqw;
      symm at hh;
      subst weqx; subst tseqw;
      have xx := Term.neutral_form_appk_rev_exists hh; cases xx;
      case _ fnfp =>
        have hh := fnfp.2; subst hh; simp_all;
        have hh1 := hh.1; have hh2 := hh.2;
        have xterm : Γ.is_term x = true := by simp; unfold Frame.is_term; rw[<-x_term];
        have x_not_stable := Frame.is_term_implies_not_is_stable_red xterm; apply (x_not_stable x_stable);
case _ Γ f _ _ a fj _ _ _ _ h =>
  cases h;
  case _ =>
    have lem := classification_lemma fj; simp at lem;
    cases lem;
    case _ => simp_all; sorry
    case _ =>  sorry

  case _ T x sp t x_term fanf =>
    symm at fanf; have fanf := Term.neutral_form_appk_rev_exists fanf;
    cases fanf; case _ fsp fanf =>
    symm at x_term; symm at fanf;
    have xx := ctx_get_term_well_typed wΓ x_term;
    have xx' := ctx_get_term_type_kind wΓ x_term;
    have lem := classification_lemma xx.1; simp at lem; cases lem;
    case _ h => subst h; cases xx'.2;
    case _ h =>
      cases h;
      case _ h => have uniq := uniqueness_of_types xx'.2 h; simp_all;
      case _ h => sorry
          -- cases h; case _ h =>
          --   have uniq := uniqueness_of_types xx' h.2; subst uniq;
          --   have f_form := Term.neutral_form_law fp; subst f_form; simp_all;
          --   case _ fj => sorry
case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ h' _ h =>
  rw[Option.bind_eq_some] at h;
  cases h'
  case _ => simp_all;
  case _ => sorry
  case _ => sorry
  case _ => sorry
case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ h' _ h =>
  rw[Option.bind_eq_some] at h;
  cases h; case _ fnf =>
    cases h';
    case _ => simp_all
    case _ => simp_all; sorry
    case _ => sorry
    case _ => sorry
case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all


theorem term_neutral_form_peel :
   (f `@ t).neutral_form = .none ->
   f.neutral_form = .none := by
intros ft;
induction f generalizing t
any_goals (solve | simp_all)
case _ => sorry

theorem term_neutral_form_peel_appk :
   (f `@k t).neutral_form = .none ->
   f.neutral_form = .none := by
intros ft;
induction f generalizing t
any_goals (solve | simp_all)
case _ => sorry


-- s is a value, cannot have a neutral form; datatype type, is impossible
theorem term_neutral_form_datatype :
  Val Γ t ->
  t.neutral_form = .none ->
  ValidHeadVariable T Γ.is_datatype ->
  Γ ⊢ t : T ->
  False := by
intros tv nf vhv tJ;
induction tv;
any_goals (solve | simp_all)
any_goals (solve | cases tJ; cases vhv; simp_all)
case _ Γ f h =>
  cases tJ; case _ A argJ fJ =>
  have xx := term_neutral_form_peel_appk nf;
  sorry

 -- cases vhv; case _ w h =>
 --  have lem := classification_lemma tJ; simp at lem;
 --  cases lem;
 --  case _ => simp_all
 --  case _ h' =>
 --    have xx := term_neutral_form_peel_appk nf;

 --    cases h';
 --    case _ h =>  sorry
 --    case _ h => simp_all; cases h; case _ w h => sorry


theorem term_neutral_form_opent :
  Val Γ t ->
  t.neutral_form = .none ->
  ValidHeadVariable T Γ.is_opent ->
  Γ ⊢ t : T ->
  False := by
intros tv nf vhv tJ;

sorry


theorem var_type_lemma : Γ.is_stable_red n -> Γ ⊢ (#n).apply_spine ts : (A ~ B) -> False := by
intros n_stable h; induction ts;
case _ => simp_all; cases h; case _ wΓ ty => symm at ty;  apply (ctx_get_var_no_eq_type wΓ n_stable ty);
case _ hd tl ih =>
   sorry

theorem refl_is_val : DeclCtx Γ -> Γ ⊢ η : (A ~ B)
                    -> Val Γ η
                    -> η = refl! A ∧ A = B := by
intros dctx ηJ vη; induction vη;
any_goals(solve | cases ηJ)
case _ Γ t n ts tnf n_stable =>
     symm at tnf; replace tnf := Term.neutral_form_law tnf;
     subst tnf;
     exfalso;
     apply (var_type_lemma n_stable ηJ);
case _ => cases ηJ; case _ fJ =>
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h; case _ h => have h := invert_eq_kind h; cases h;
  case _ h => cases h; case _ h => simp_all; cases h.2; cases h.1
case _ => cases ηJ; simp_all

theorem ctor_uniqueness {Γ : Ctx Term}: (Γ.is_ctor x = true) -> (Γ.is_ctor y = false) -> x ≠ y := by
intros xctor yctor xeqy ;
induction Γ;
case _ => simp_all
case _ here there ih =>
  unfold Ctx.is_ctor at xctor; unfold dnth at xctor;
  split at xctor;
  case _ => simp_all;
  case _ =>
    simp_all; subst xeqy;
    unfold dnth at yctor; simp_all;
  case _ =>
    simp_all; subst xeqy;
    unfold dnth at yctor; simp_all;

theorem insttype_uniqueness {Γ : Ctx Term}: (Γ.is_insttype x = true) -> (Γ.is_insttype y = false) -> x ≠ y := by
intros xinst yinst xeqy ;
induction Γ;
case _ => simp_all
case _ here there ih =>
  unfold Ctx.is_insttype at xinst; unfold dnth at xinst;
  split at xinst;
  case _ => simp_all;
  case _ =>
    simp_all; subst xeqy;
    unfold dnth at yinst; simp_all;
  case _ =>
    simp_all; subst xeqy;
    unfold dnth at yinst; simp_all;


-- this is stupid
theorem bool_implication (x : Bool) : x = false -> ¬ x = true :=
by intro h; rw [h]; simp


theorem head_cannot_be_empty :
   DeclCtx Γ ->
   Γ ⊢ t : T ->
   .some (x, sp) = Term.neutral_form t ->
   ¬ Γ d@ x  = .empty
:= by
intros dctx tJ tnf x_empty;
induction sp
case _ =>
  simp_all;
  have xx' := Term.neutral_form_law tnf; unfold Term.apply_spine at xx';
  rw [<-xx'] at tJ;
  cases tJ; case _ h => rw [x_empty] at h; unfold Frame.get_type at h; simp at h
case _ ht tl ih =>
  have xx := Term.neutral_form_law tnf;
  induction t;
  any_goals(solve | simp_all)
  case _ => sorry


theorem unstable_var_steps :
   DeclCtx Γ ->
   Γ ⊢ t : T ->
   .some (x, sp) = Term.neutral_form t ->
   (Γ.is_stable_red x = false) ->
   ∃ t', Red Γ t t'
:= by
intros dctx tJ tnf x_not_stable;
have x_not_stable := @bool_implication (Γ.is_stable_red x) x_not_stable;
generalize xx : Γ d@ x = f;
cases f;
any_goals (solve | unfold Ctx.is_stable_red at x_not_stable
                   rw [xx] at x_not_stable
                   simp at x_not_stable
                   unfold Frame.is_stable_red at x_not_stable
                   simp at x_not_stable)
case empty =>
  have no_empty := (head_cannot_be_empty dctx tJ tnf);
  exfalso; apply (no_empty xx)
case type => unfold DeclCtx at dctx; have xx := @dctx x; simp_all;
case term lt =>
  symm at xx; have reds := Red.letterm tnf xx;
  apply Exists.intro [lt.apply_spine sp] reds;
case openm =>
   have om : (Γ d@ x).is_openm := by unfold Frame.is_openm; rw [xx];
   generalize isp : instance_indices Γ 0 x [] = ιs at *; symm at isp;
   generalize instsp : get_instances Γ ιs = insts at *; symm at instsp;
   generalize instsp' : List.map (·.apply_spine sp) insts = insts' at *; symm at instsp';
   apply (Exists.intro insts' (Red.inst tnf om isp instsp instsp'))


@[simp]
abbrev StepOrVal : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , _) => Val Γ t ∨ ∃ t', Red Γ t t'
| .wf  => λ _ => λ () => true

theorem progress :
   ⊢ Γ -> DeclCtx Γ
  -> Judgment v Γ ix
--------------------------------------
  -> StepOrVal v Γ ix := by
intros wΓ dctx j; induction j;
any_goals (solve | simp_all)
case _ Γ A t b _ _ _ _ _ _ _ ih _ =>
  simp_all;
  generalize tl' : [b β[ t ]] = t' at *; symm at tl';
  have reds := @Red.letbeta Γ A t b; rw [<-tl']  at reds;
  have ereds : ∃ t', Red Γ (.letterm A t b) t' := Exists.intro t' reds;
  apply Or.inr ereds;

case _ => simp_all; apply Or.inl Val.star;
case var Γ x _ _ xTy ih =>
  simp at ih;
  unfold Frame.get_type at xTy; simp at xTy;
  split at xTy;
  any_goals (solve | simp_all)
  case _ f _ x_is_kind => -- bogus case
    simp_all; have xK := ctx_get_var_type wΓ x_is_kind;
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    have k_st_red : Γ.is_stable_red x := by simp; unfold Frame.is_stable_red; rw [x_is_kind]
    apply Or.inl (Val.app hh k_st_red);
  case _ f _ x_is_type => exfalso; apply no_lam_bindings dctx x x_is_type;
  case _ f _ x_is_datatype =>
      simp_all; have x_is_stable := dt_is_stable x_is_datatype;
      have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
      apply Or.inl;
      apply Val.app hh x_is_stable;
  case _ f t x_is_ctor =>
    have xx : Frame.is_stable_red (Γ d@ x) := by unfold Frame.is_stable_red; rw[x_is_ctor];
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    apply Or.inl (Val.app hh xx)
  case _ x_is_opent =>
      have x_is_stable := opent_is_stable x_is_opent;
      have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
      apply Or.inl;
      apply Val.app hh x_is_stable;
  case _ x_is_openm =>  -- steps inst
    have nf  := @Term.var_neutral_form x; symm at nf;
    have om : (Γ d@ x).is_openm := by unfold Frame.is_openm; rw [x_is_openm];
    generalize isp : instance_indices Γ 0 x [] = ιs at *; symm at isp;
    generalize instsp : get_instances Γ ιs = insts at *; symm at instsp;
    generalize instsp' : List.map (·.apply_spine []) insts = insts' at *; symm at instsp';
    apply Or.inr (Exists.intro insts' (Red.inst nf om isp instsp instsp'))
  case _ x_is_insttype =>  -- value
    have xx : Frame.is_stable_red (Γ d@ x) := by unfold Frame.is_stable_red; rw[x_is_insttype];
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    apply Or.inl (Val.app hh xx)
  case _ A t x_frame =>  -- steps letterm
    have nf : .some (x, []) = (#x).neutral_form := Term.var_neutral_form;
    have x_is_term : .term A t = Γ d@ x := by symm at x_frame; apply x_frame
    generalize tlp : [t.apply_spine []] = t' at *; symm at tlp;
    have etl' : ∃ t', Red Γ (#x) t' := Exists.intro ([t.apply_spine []]) (Red.letterm nf x_is_term);
    apply Or.inr etl'

case _ => simp_all; apply Or.inl; apply Val.arrk
case _ => simp_all; apply Or.inl; apply Val.all
case _ => simp_all; apply Or.inl; apply Val.arr

case appk fs as => simp_all;  apply Or.inl; apply Val.appk

case _ => simp_all; apply Or.inl; apply Val.eq

case ite Γ p A s _ i _ _ e _ sJ RJ _ vhvp vhvr stm _ tstar _ ps ss _ is _ es =>
  cases vhvp; case _ pf h =>
    have pnf := h.1; have hpctor := h.2;
    have p_n := pf.1; have p_sp := pf.2;
    generalize snf : s.neutral_form = xx at *; symm at snf;
    cases xx;
    case _ =>
       cases (ss wΓ dctx)
       case _ h => exfalso; symm at snf; apply (term_neutral_form_datatype h snf vhvr sJ)
       case _ h => cases h; case _ w h =>
          generalize tlp : List.map (Term.ite p · i e) w = tl' at *; symm at tlp;
          have reds : ∃ t', Red Γ (.ite p s i e) t' := Exists.intro tl' (Red.ite_congr h tlp);
          apply Or.inr reds
    case _ sf =>
       simp;
       have s_sp := sf.2;
       generalize sp : sf.1 = s_n at *; symm at sp;
       generalize s_spp : sf.2 = s_sp at *; symm at s_spp;
       generalize snctor : Γ.is_ctor s_n = p at *;
       have s_form := Term.neutral_form_law snf; rw[<-s_spp] at s_form; rw[<-sp] at s_form;
       cases p;
       case _ => -- scrutinee is a not ctor headed but has a neutral form
         generalize xx : Γ.is_stable_red s_n = x_is_stable;
         cases x_is_stable;
         case false =>
           apply Or.inr; simp at xx; rw[sp] at xx;
           have reds' := unstable_var_steps dctx sJ snf xx;
           cases reds'; case _ w sreds =>
           generalize tlp : List.map (Term.ite p · i e) w = tl at *; symm at tlp;
           have reds : ∃ t', Red Γ (.ite p s i e) t' := Exists.intro tl (Red.ite_congr sreds tlp)
           apply reds
         case true =>
           generalize xx' : Γ d@ s_n = f;
           cases f;
           any_goals (solve | unfold Ctx.is_stable_red at xx; rw [xx'] at xx; unfold Frame.is_stable_red at xx; simp at xx)
           any_goals (solve | subst sp;
                              have reds : ∃ t', Red Γ (.ite p s i e) t' :=
                                Exists.intro [e] (Red.ite_missed pnf snf xx (Or.inl (ctor_uniqueness hpctor snctor)));
                              apply Or.inr; apply reds)

       case _ =>
          have check := Nat.decEq pf.fst sf.fst;
          cases check;
          case _ h =>
            have s_is_stable : Γ.is_stable_red sf.fst := by rw[sp] at snctor; apply Frame.is_ctor_implies_is_stable_red snctor;
            have reds : ∃ t', Red Γ (.ite p s i e) t' := Exists.intro [e] (Red.ite_missed pnf snf s_is_stable (Or.inl h));
            apply Or.inr; apply reds;
          case _ h =>
            generalize comp_prefix : prefix_equal pf.snd sf.snd = h at *;
            cases h
            case _ h =>
              have s_is_stable : Γ.is_stable_red sf.fst := by rw[sp] at snctor; apply Frame.is_ctor_implies_is_stable_red snctor;
              have reds : ∃ t', Red Γ (.ite p s i e) t' :=
                   Exists.intro [e] (Red.ite_missed pnf snf s_is_stable (Or.inr comp_prefix));
              apply Or.inr; apply reds;
            case _ h' =>
              symm at comp_prefix;
              have sfp : sf = (sf.fst , sf.snd) := by simp_all;
              rw [sfp] at snf; rw[<-h] at snf;
              have reds : ∃ t', Red Γ (.ite p s i e) t' :=
                Exists.intro [i.apply_spine h'] (Red.ite_matched pnf snf comp_prefix hpctor);
              apply Or.inr; apply reds;

case guard Γ p A s R t _ _ pJ sJ _ _ vhvp vhvr _ _ _  ps ss _ _ _  =>
  cases vhvp; case _ pf h =>
    have pnf := h.1; have hpctor := h.2;
    have p_n := pf.1; have p_sp := pf.2;
    generalize snf : s.neutral_form = xx at *; symm at snf;
    cases xx;
    case _ =>
       cases (ss wΓ dctx)
       case _ h => exfalso; symm at snf; apply (term_neutral_form_opent h snf vhvr sJ)
       case _ h => cases h; case _ w h =>
          generalize tlp : List.map (Term.guard p · t) w = tl' at *; symm at tlp;
          have reds : ∃ t', Red Γ (.guard p s t) t' := Exists.intro tl' (Red.guard_congr h tlp);
          apply Or.inr reds
    case _ sf =>
       simp
       generalize snctor : Γ.is_insttype sf.fst = p at *;
       generalize sp : sf.1 = s_n at *; symm at sp;
       generalize s_spp : sf.2 = s_sp at *; symm at s_spp;
       have s_form := Term.neutral_form_law snf; rw[<-s_spp] at s_form; rw[<-sp] at s_form;
       cases p;
       case _ =>   -- scrutinee is a not a opentype headed but has a neutral form
         generalize xx : Γ.is_stable_red s_n = x_is_stable;
         cases x_is_stable;
         case false =>
           apply Or.inr; simp at xx; rw[sp] at xx;
           have reds' := unstable_var_steps dctx sJ snf xx;
           cases reds'; case _ w sreds =>
           generalize tlp : List.map (Term.guard p · t) w = tl at *; symm at tlp;
           have reds : ∃ t', Red Γ (Term.guard p s t) t' := Exists.intro tl (Red.guard_congr sreds tlp)
           apply reds
         case true =>
           generalize xx' : Γ d@ s_n = f;
           cases f;
           any_goals (solve | unfold Ctx.is_stable_red at xx; rw [xx'] at xx; unfold Frame.is_stable_red at xx; simp at xx)
           any_goals (solve | subst sp;
                              have reds : ∃ t', Red Γ (.guard p s t) t' :=
                                Exists.intro [] (Red.guard_missed pnf snf xx (Or.inl (insttype_uniqueness hpctor snctor)));
                              apply Or.inr; apply reds)
       case _ =>
          have check := Nat.decEq pf.fst sf.fst;
          cases check;
          case _ h =>
            have s_is_stable : Γ.is_stable_red sf.fst := by rw[sp] at snctor; apply Frame.is_insttype_implies_is_stable_red snctor;
            have reds : ∃ t', Red Γ (.guard p s t) t' := Exists.intro [] (Red.guard_missed pnf snf s_is_stable (Or.inl h));
            apply Or.inr; apply reds; -- sorry
          case _ h =>
            generalize comp_prefix : prefix_equal pf.snd sf.snd = h at *;
            cases h
            case _ h =>
              have s_is_stable : Γ.is_stable_red sf.fst := by rw[sp] at snctor; apply Frame.is_insttype_implies_is_stable_red snctor;
              have reds : ∃ t', Red Γ (.guard p s t) t' :=
                   Exists.intro [] (Red.guard_missed pnf snf s_is_stable (Or.inr comp_prefix));
              apply Or.inr; apply reds;
            case _ h' =>
              symm at comp_prefix;
              have sfp : sf = (sf.fst , sf.snd) := by simp_all;
              rw [sfp] at snf; rw[<-h] at snf;
              have reds : ∃ t', Red Γ (.guard p s t) t' :=
                Exists.intro [t.apply_spine h'] (Red.guard_matched pnf snf comp_prefix);
              apply Or.inr; apply reds;

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lam

case app Γ f A B a B' fJ aJ _ fs as =>
  simp_all; cases fs;
  case inl h => -- f is value
    cases h;
    case app n ts n_stable fnf =>
       have fanf := @Term.neutral_form_app f a n ts fnf;
       apply Or.inl (Val.app fanf n_stable);
    case lam A B =>
      apply Or.inr;
      have reds : ∃ t', Red Γ ((`λ[A]B) `@ a) t' := Exists.intro [B β[ a ]] (@Red.beta Γ A B a);
      apply reds
    case lamt  => have xx := lamt_typing_unique fJ; cases xx; case _ w h => cases h;
    case refl => have xx := refl_typing_unique fJ; cases xx
    case _ => cases fJ; case _ fJ' =>
      have lem := classification_lemma fJ'; simp at lem; cases lem;
      case _ h => cases h; case _ h => cases h;
      case _ h => cases h; case _ h => cases h.2; cases h.1;
    case _ => have fJ' := Judgment.ax wΓ; have u := uniqueness_of_types fJ fJ'; cases u;
    case _ => cases fJ
    case _ => cases fJ;
    case _ => cases fJ
    case _ => cases fJ

  case inr h => cases h; case _ w h => -- f steps
    generalize tlp : List.map (· `@ a) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (f `@ a) t' := Exists.intro tl' (Red.app_congr h tlp);
    apply Or.inr reds

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lamt

case appt Γ f _ _ a _ fJ aJ _ fs as =>
  simp_all; cases fs;
  case inr h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· `@t a) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (f `@t a) t' := Exists.intro tl' (Red.appt_congr h tlp);
      apply reds;
  case inl h =>
    cases h;
    case app n ts n_stable fnf =>
      have fanf := @Term.neutral_form_appt f a n ts fnf
      apply Or.inl;
      apply (Val.app fanf n_stable);
    case lam => have xx := lam_typing_unique fJ; cases xx; simp_all;
    case lamt a' b =>
      apply Or.inr;
      have reds : ∃ t', Red Γ ((Λ[a']b) `@t a) t' := Exists.intro [b β[ a ]] (@Red.betat Γ a' b a);
      apply reds
    case refl => have xx := refl_typing_unique fJ; cases xx
    case _ => cases fJ; case _ fJ' =>
      have lem := classification_lemma fJ'; simp at lem; cases lem;
      case _ h => cases h; case _ h => cases h;
      case _ h => cases h; case _ h => cases h.2; cases h.1;
    case _ => have fJ' := Judgment.ax wΓ; have xx := uniqueness_of_types fJ fJ'; cases xx
    case _ => cases fJ
    case _ => cases fJ
    case _ => cases fJ
    case _ => cases fJ

case _ Γ t A η B tJ ηJ ts cs =>
  simp_all; cases cs;
  case _ h =>
      have ηreflp := @refl_is_val Γ η A B dctx ηJ h;
      have ηrefl := ηreflp.1;
      subst ηrefl; apply Or.inr;
      have reds : ∃ t', Red Γ (t ▹ refl! A) t' := Exists.intro [t] Red.cast;
      apply reds
  case _ h => cases h; case _ w h =>
      apply Or.inr
      generalize tlp : List.map (t ▹ ·) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (t ▹ η) t' := Exists.intro tl' (Red.cast_congr h tlp);
      apply reds;

case _ => apply Or.inl Val.refl
case sym Γ η A B ηJ ηs =>
  cases ηs wΓ dctx;
  case _ h =>
    have x := refl_is_val dctx ηJ h;
    have xeqrefl := x.left;
    have aeqB := x.right;
    subst xeqrefl;
    apply Or.inr
    have reds : ∃ t', Red Γ (sym! refl! A) t' := Exists.intro [refl! A] (@Red.sym Γ A);
    apply reds;
  case _ ηreds => cases ηreds; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (sym! ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (sym! η) t' := Exists.intro tl' (Red.sym_congr h tlp);
    apply reds;

case seq Γ η1 A B η2 C η1J η2J η1s η2s =>
  simp_all; cases η2s;
  case _ h =>
    have η2refp := refl_is_val dctx η2J h;
    have η2refl := η2refp.1; cases η1s;
    case _ h =>
      have η1refp := refl_is_val dctx η1J h;
      have η1refl := η1refp.1; have aeqB := η1refp.2; have BeqC := η2refp.2
      subst η1refl; subst η2refl;
      apply Or.inr; subst aeqB;
      have reds : ∃ t', Red Γ ((refl! A) `; (refl! A)) t' := Exists.intro [refl! A] Red.seq;
      apply reds
    case _ h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· `; η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `; η2) t' := Exists.intro tl' (Red.seq_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (η1 `; ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `; η2) t' := Exists.intro tl' (Red.seq_congr2 h tlp);
    apply reds

case appc Γ A K1 K2 B η1 C D η2 aK bK η1J cJ dJ η2J _ _ η1s _ _ η2s  =>
  -- check if η1 reduces or η2 reduces if both are values then reduce to refl
  simp_all; cases η2s;
  case _ h =>
    have η2refp := refl_is_val dctx η2J h;
    have η2refl := η2refp.1; cases η1s;
    case _ h =>
      have η1refp := refl_is_val dctx η1J h;
      have η1refl := η1refp.1; -- have aeqB := η1refp.2; have BeqC := η2refp.2
      subst η1refl; subst η2refl;
      apply Or.inr;
      have reds : ∃ t', Red Γ ((refl! A) `@c (refl! C)) t' := Exists.intro [refl! (A `@k C)] Red.appc;
      apply reds
    case _ h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· `@c η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `@c η2) t' := Exists.intro tl' (Red.appc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (η1 `@c ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `@c η2) t' := Exists.intro tl' (Red.appc_congr2 h tlp);
    apply reds

case arrowc Γ A B η1 C D η2 _ _ η1J _ _ η2J _ _ η1s _ _ η2s =>
  simp_all; cases η2s (Judgment.wfempty wΓ) (DeclCtx.consempty dctx);
  case _ h =>
    have dctx' : DeclCtx (Frame.empty :: Γ) := DeclCtx.consempty dctx;
    have η2refp := refl_is_val dctx' η2J h;
    have η2refl := η2refp.1; cases η1s;
    case _ h =>
      have η1refp := refl_is_val dctx η1J h;
      have η1refl := η1refp.1;
      subst η1refl; subst η2refl;
      apply Or.inr;
      have reds : ∃ t', Red Γ (refl!(A) -c> refl! C) t' := Exists.intro [(refl! (A -t> C))] Red.arrowc;
      apply reds
    case _ h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· -c> η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 -c> η2) t' := Exists.intro tl' (Red.arrowc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (η1 -c> ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 -c> η2) t' := Exists.intro tl' (Red.arrowc_congr2 h tlp);
    apply reds

case fst Γ A _ _ _ η C _ _ _ ηJ _ _ ηs =>
  simp_all; cases ηs;
  case inl h =>
    have ηrp := refl_is_val dctx ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    apply Or.inr;
    have reds : ∃ t', Red Γ ((refl! (A `@k C)).!1) t' := Exists.intro [refl! A] Red.fst;
    apply reds;
  case inr h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (·.!1) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η.!1) t' := Exists.intro tl' (Red.fst_congr h tlp);
    apply reds

case snd Γ _ C _ η A _ _ _ _ ηJ _ _ _ ηs =>
  simp_all; cases ηs;
  case inl h =>
    have ηrp := refl_is_val dctx ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    apply Or.inr;
    have reds : ∃ t', Red Γ ((refl! (A `@k C)).!2) t' := Exists.intro [refl! C] Red.snd;
    apply reds;
  case inr h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (·.!2) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η.!2) t' := Exists.intro tl' (Red.snd_congr h tlp);
    apply reds

case _ Γ K A B η allAJ allBJ ηJ _ _ ts =>
  cases allAJ; case _ kkind _ =>
  have ts := ts (Judgment.wfkind kkind wΓ) (DeclCtx.conskind dctx);
  cases ts;
  case inr h => cases h; case _ w h =>
    simp_all;
    apply Or.inr;
    generalize tlp : List.map (∀c[K]·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (∀c[K] η) t' := Exists.intro tl' (Red.allc_congr h tlp);
    apply reds
  case inl h =>
    have ηrp := refl_is_val (DeclCtx.conskind dctx) ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    apply Or.inr;
    have reds : ∃ t', Red Γ ((∀c[K] refl! A)) t' := Exists.intro [refl! (∀[K]A)] Red.allc;
    apply reds;

case _ Γ η1 K A B C D η2 _ _ η1J CKJ _ η2J _ _ η1s _ _ η2s =>
  simp_all; cases η2s;
  case _ h =>
    have η2refp := refl_is_val dctx η2J h;
    have η2refl := η2refp.1; cases η1s;
    case _ h =>
      have η1refp := refl_is_val dctx η1J h;
      have η1refl := η1refp.1;
      subst η1refl; subst η2refl;
      apply Or.inr;
      have reds : ∃ t', Red Γ (refl!(∀[K] A) `@c[refl! C]) t' := Exists.intro [refl! (A β[ C ])] Red.apptc;
      apply reds
    case _ h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· `@c[η2]) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `@c[η2]) t' := Exists.intro tl' (Red.apptc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    apply Or.inr;
    generalize tlp : List.map (η1 `@c[·]) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `@c[η2]) t' := Exists.intro tl' (Red.apptc_congr2 h tlp);
    apply reds
