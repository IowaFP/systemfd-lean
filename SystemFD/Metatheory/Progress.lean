
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Reduction

inductive Neutral : Ctx Term -> Term -> Prop where
  | varNe : ¬ Γ.is_stable n
          -> Neutral Γ (#n)
  | iteNe : Neutral Γ s -> Neutral Γ (.ite p s b c)
  | guardNe : Neutral Γ s -> Neutral Γ (.guard p s c)
  | appNe : Neutral Γ t
          -> Neutral  Γ  (t `@ t')
  | apptNe : Neutral Γ t
           -> Neutral Γ (t `@t t')
  | castNe : Neutral  Γ η
           -> Neutral Γ (t ▹ η)
  | fstNe : Neutral Γ η
          -> Neutral  Γ (η .!1)
  | sndNe : Neutral  Γ η
          -> Neutral Γ (η .!2)
  | symNe : Neutral  Γ η
         -> Neutral  Γ (sym! η)
  | seq1 : Neutral  Γ η
         -> Neutral  Γ (η `; η')
  | seq2 : Neutral  Γ η'
         -> Neutral  Γ (η `; η')

inductive Val : Ctx Term -> Term -> Prop where
  | app : t.neutral_form = .some (n, ts)
        -> Γ.is_stable n
        -> Val Γ t
  | lam :  Val Γ (`λ[a] b)
  | lamt : Val Γ (Λ[A] b)
  | refl : Val Γ (refl! _)

theorem flip_eq : Γ ⊢ (A ~ B) : ★ -> Γ ⊢ (B ~ A) : ★ := by
intros h; cases h; case _ k AJ BJ => apply Judgment.eq k BJ AJ


theorem opent_kind : ⊢ Γ -> Γ d@ x = .opent t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry

theorem datatype_kind : ⊢ Γ -> Γ d@ x = .datatype t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry

theorem not_neutral_form_shape : Val Γ t ->
        t.neutral_form = .some (n, ts)
        -> ¬ ((t = `λ[A] b)
            ∨ (t = Λ[A] b)
            ∨ t = .letterm A t' b
            ∨ t = .guard p s b
            ∨ t = .ite p s b c
            ∨ t = .kind
            ∨ t = .type
            ∨ t = refl! A
            ∨ t = sym! η
            ) := by
intros tnf; induction t;
any_goals (solve | simp_all)

-- theorem neutral_form_shape : Val Γ t ->
--         t.neutral_form = .some (n, ts)
--         -> ¬ ((t = (f `@ a))
--             ∨ (t = (f `@t a))
--             ∨ (t = (f `@k a))
--             ) := by
-- intros tnf; induction t;
-- any_goals (solve | simp_all)


theorem invert_eq_kind : Γ ⊢ (A ~ B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_arr_kind : Γ ⊢ (A -t> B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_all_kind : (Γ ⊢ ∀[ A ] B : w) -> w = ★ := by
intros eqJ; cases eqJ; simp_all;


theorem test : ⊢ Γ -> ¬ Γ.is_stable x -> ¬ (Γ d@ x).get_type = .some (A ~ B) := by sorry

def DeclCtx (Γ : Ctx Term) : Prop := ∀ n, ¬ Γ.is_lam_bound n

theorem invert_appk_val : Γ ⊢ t : (A -k> B)
                       -> Val Γ t -> t.neutral_form = .none
                       -> t = Λ[A] t' := by
intros tJ vt tnotnormal; induction vt;
case _ => simp_all
case _ => cases tJ
case _ => cases tJ
case _ => cases tJ


theorem lamt_typing_unique : Γ ⊢ Λ[A]b : t -> ∃ B', t = ∀[A] B' := by
intros tJ; cases tJ;
case _ => simp_all;

theorem lam_typing_unique : Γ ⊢ `λ[a]b : t -> ∃ A' B', (t = (A' -t> B')) := by
intros tJ; cases tJ;
case _ => simp_all;

theorem refl_typing_unique : Γ ⊢ refl! A : t -> (t = (A ~ A)) := by
intros tJ; cases tJ;
case _ => simp_all;

theorem apptneqrefl : ¬ ((f `@t a) = (refl! A)) := by simp_all
theorem appneqrefl : ¬ ((f `@ a) = (refl! A)) := by simp_all

theorem openm_no_stable {Γ : Ctx Term}{n : Nat} :
  Frame.is_openm (Γ d@ n) = true -> ¬ (Frame.is_stable (Γ d@ n)) := by
intros om; simp_all; unfold Frame.is_openm at om; split at om;
case _ => unfold Frame.is_stable; simp_all;
case _ => simp_all

theorem stable_no_reduce : t.neutral_form = .some (n, sp) -> Γ.is_stable n = true -> ¬ ∃ t', Red Γ t t' := by
intros tnf nstable x; cases x;
  case _ w h =>
  simp_all; induction h generalizing n sp;
  any_goals (solve | simp_all)
  case _ Γ _ _ _ _ om _ _ nstable =>
    have n_not_stable := openm_no_stable om;
    simp_all;
  case _ hnf idx =>
    unfold Frame.is_stable at nstable; symm at hnf;
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

theorem val_no_red : Val Γ t -> ¬ ∃ t', Red Γ t t' := by
intros vt tred; induction vt;
case _ =>
  cases tred; case _ nf st w h =>
    have no_red := stable_no_reduce nf st;
    have reds := Exists.intro w h; simp_all;
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all
  case _ => simp_all

theorem refl_is_val : DeclCtx Γ -> Γ ⊢ η : (A ~ B)
                    -> Val Γ η
                    -> η = refl! A ∧ A = B := by
intros dctx ηJ vη; induction vη;
case _ Γ t n _ _ n_stable =>
  have lem := classification_lemma ηJ; simp at lem;
  cases lem; case _ j => cases j;
  case _ h =>
  cases h; case _ w h =>
  have weqstr := invert_eq_kind h.2
  subst weqstr;
  unfold Ctx.is_stable at n_stable;
  unfold Frame.is_stable at n_stable;
  split at n_stable;
  any_goals (solve | simp_all);
  case _ ts tnf _ _ _ _ _ _ =>
    cases t;
    any_goals (solve | simp_all)
    case _ a =>
      have anf' : ((#a).neutral_form = .some (a, [])) := @Term.var_neutral_form a;
      rw [anf'] at tnf; injection tnf with aeqs; simp_all; cases ηJ;
      case _ wΓ _  =>
        have xx := @test Γ n A B wΓ sorry; simp_all;
    case _ ctor2v _ _  =>
    cases ctor2v;
    any_goals (solve | cases ηJ)
    case _  =>
      cases ηJ; case _ aj =>
      have lem := classification_lemma aj; simp at lem;
      cases lem;
      case _ h => cases h; case _ h => cases h;
      case _ h => cases h; case _ w h => cases h.2; case _ h => cases h.1;
    case appt f a =>
      cases ηJ; case _ _ _ aj _ _ =>
      have lem := classification_lemma aj; simp at lem; cases lem;
      case _ h => cases h
      case _ h =>
        cases h; case _ h => cases h.2; case _ h => simp_all; cases h.2; case _ h =>
        simp_all; rw[Option.bind_eq_some] at tnf; simp at tnf; cases tnf; case _ w h =>
        cases h; case _ w ts' h =>
        have weqn := h.2.1; symm at weqn; subst weqn; simp at h;
        have fff := @apptneqrefl f a A;
        sorry
    case app => cases ηJ; case _ aj _ _ =>
      have lem := classification_lemma aj; simp at lem;
      cases lem;
      case _ h => cases h
      case _ h => cases h; case _ w h => cases h; case _ f a _ _ _ _ _ w h =>
        cases h; case _ h => simp_all; rw [Option.bind_eq_some] at *; sorry
    case _ => cases ηJ; case _ aj =>
      have lem := classification_lemma aj; simp at lem;
      cases lem;
      case _ h => cases h
      case _ h => cases h; case _ w h => cases h.2; case _ h => cases h.2; simp_all;
    case _ => cases ηJ; case _ s _ _ aj => simp_all;
    case _ => cases ηJ; case _ aj => cases h; case _ h => cases h; simp_all
    case _ => cases ηJ; case _ aj _ _ _ =>
      have lem := classification_lemma aj; simp at lem; cases lem;
      case _ h => cases h
      case _ h => cases h; case _ h => cases h.2; simp_all;

case _ => cases ηJ
case _ => cases ηJ
case _ => cases ηJ; simp_all


@[simp]
abbrev StepOrVal : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , A) => DeclCtx Γ -> (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K) -> Val Γ t ∨ ∃ t', Red Γ t t'
| .wf  => λ _ => λ () => true


theorem progress :
   ⊢ Γ
  -> Judgment v Γ ix
--------------------------------------
  -> StepOrVal v Γ ix := by
intros wΓ j; induction j;
any_goals (solve | simp at *)
all_goals (intro dctx h)
case _ Γ A t b _ _ _ _ _ _ _ ih _ =>
  simp_all;
  generalize tl' : [b β[ t ]] = t' at *; symm at tl';
  have reds := @Red.letbeta Γ A t b; rw [<-tl']  at reds;
  have ereds : ∃ t', Red Γ (.letterm A t b) t' := Exists.intro t' reds;
  apply Or.inr ereds;

case _ => cases h; case _ h => cases h.2;
case var Γ x _ _ xTy ih =>
  simp at ih; have x_no_lam := dctx x;
  unfold Ctx.is_lam_bound at x_no_lam;
  unfold Frame.is_lam_bound at x_no_lam;
  unfold Frame.get_type at xTy; simp at xTy;
  split at xTy;
  any_goals (solve | simp_all)
  case _ x_is_datatype => cases h; case _ w h =>
    cases h; case _ w h =>
      injection xTy with xt; subst xt;
      have lem := classification_lemma h; simp at lem; cases lem;
      case _ h => subst h; cases w
      case _ h =>
        simp_all; have lem := classification_lemma h; simp at lem; cases lem;
        case _ h => cases h; cases w
        case _ =>
             have ttt := datatype_kind wΓ x_is_datatype;
             have ut := uniqueness_of_types ttt h; subst ut; cases w;

  case _ f t x_is_ctor =>
    have xx : Frame.is_stable (Γ d@ x) := by unfold Frame.is_stable; rw[x_is_ctor];
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    apply Or.inl (Val.app hh xx)
  case _ x_is_opent =>
    injection xTy with teqT; symm at teqT; subst teqT;   -- classification lemma
    cases h; case _ h =>
      cases h; case _ t w _ h =>
      simp_all;
      have lem := classification_lemma h; simp at lem; cases lem;
      case _ l h => subst h; cases l
      case _ l _ =>
        have ttt := opent_kind wΓ x_is_opent;
        have ut := uniqueness_of_types ttt h; subst ut; cases l;

  case _ x_is_openm =>  -- steps inst
    have nf  := @Term.var_neutral_form x; symm at nf;
    have om : (Γ d@ x).is_openm := by unfold Frame.is_openm; rw [x_is_openm];
    generalize isp : instance_indices' Γ 0 x [] = ιs at *; symm at isp;
    generalize instsp : get_instances Γ ιs = insts at *; symm at instsp;
    generalize instsp' : List.map (·.apply_spine []) insts = insts' at *; symm at instsp';
    apply Or.inr (Exists.intro insts' (Red.inst nf om isp instsp instsp'))
  case _ x_is_insttype =>  -- value
    have xx : Frame.is_stable (Γ d@ x) := by unfold Frame.is_stable; rw[x_is_insttype];
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    apply Or.inl (Val.app hh xx)
  case _ A t x_frame =>  -- steps letterm
    have nf : .some (x, []) = (#x).neutral_form := Term.var_neutral_form;
    have x_is_term : .term A t = Γ d@ x := by symm at x_frame; apply x_frame
    generalize tlp : [t.apply_spine []] = t' at *; symm at tlp;
    have etl' : ∃ t', Red Γ (#x) t' := Exists.intro ([t.apply_spine []]) (Red.letterm nf x_is_term);
    apply Or.inr etl'

case _ => cases h; case _ h => cases h.2
case _ => cases h; case _ h => cases h.2; cases h.1;

case _ => cases h; case _ h => cases h.2; cases h.1
case appk Γ f A B a fJ aJ  fs as =>  -- bogus case
  cases h; case _ h =>
    have lem := classification_lemma fJ; simp at lem; cases lem;
    case _ w h' => have hB := h.2; cases h'; case _ hB' =>
      have wKind := uniqueness_of_types hB hB'; subst wKind; cases h.1;
    case _ h => cases h; case _ w h => cases h.2; case _ h => cases h; case _ w h => cases w

case _ => cases h; case _ h => cases h.2; cases h.1

case ite Γ p A s _ i _ _ e _ _ _ _ _ _ _ _ tstar _ pJ sJ _ iJ _ eJ =>
  simp_all; cases h; case _ w h =>
  have weqstar := uniqueness_of_types tstar h.2; subst weqstar; simp_all;
  have pJ' := pJ ★ h.1;
  -- prefix_type_match
  sorry

case guard => sorry

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lam

case app Γ f A B a B' fJ aJ _ fs as =>
  simp_all; cases h; case _ w h =>
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h;
  case _ h => cases h; case _ w' h' =>
  have weqstar := invert_arr_kind h'.2; subst weqstar;
  cases h'.2; cases h'.1;
  have fs' := @fs ★ (h'.1) h'.2;
  cases fs';
  case inl h => -- f is value
    cases h;
    case app n ts n_stable fnf =>
      have fanf := @Term.neutral_form_app f a n ts fnf;
      apply Or.inl (Val.app fanf n_stable);
    case lam  => cases h; case _ a' b l r =>
      apply Or.inr;
      have reds : ∃ t', Red Γ ((`λ[a']b) `@ a) t' := Exists.intro [b β[ a ]] (@Red.beta Γ a' b a);
      apply reds
    case lamt =>
      cases h; case _ A' b l r =>
        have xx := lamt_typing_unique fJ; cases xx; case _ w h => cases h;
    case refl =>
        have xx := refl_typing_unique fJ; cases xx
  case inr h => cases h; case _ w h => -- f steps
    generalize tlp : List.map (· `@ a) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (f `@ a) t' := Exists.intro tl' (Red.app_congr h tlp);
    apply Or.inr reds

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lamt

case appt Γ f _ _ a _ fJ aJ _ fs as =>
  simp_all; cases h; case _ w h =>
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h
  case _ h => cases h; case _ w' h' =>
    have weqstar := invert_all_kind h'.2; subst weqstar;
    cases h'.2; cases h'.1; have fs' := @fs ★ h'.1 h'.2; cases fs';
    case inr h => cases h; case _ w h =>
      apply Or.inr;
      generalize tlp : List.map (· `@t a) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (f `@t a) t' := Exists.intro tl' (Red.appt_congr h tlp);
      apply reds
    case inl h =>
    cases h;
    case app n ts n_stable fnf =>
      have fanf := @Term.neutral_form_appt f a n ts fnf
      apply Or.inl;
      apply (Val.app fanf n_stable);
    case lam => cases h; case _ a' b l r =>
        have xx := lam_typing_unique fJ; cases xx; simp_all;
    case lamt a' b =>
      apply Or.inr;
      have reds : ∃ t', Red Γ ((Λ[a']b) `@t a) t' := Exists.intro [b β[ a ]] (@Red.betat Γ a' b a);
      apply reds
    case refl =>
        have xx := refl_typing_unique fJ; cases xx

case _ Γ t A η B tJ ηJ ts cs =>
  simp_all; cases h; case _ w h =>
  have lem := classification_lemma ηJ; simp at lem; cases lem; cases h;
  case _ eqJ _ h => cases eqJ
  case _ h => cases h; case _ w h =>
    have weqstar := invert_eq_kind h.2; subst weqstar;
    have cs' := @cs ★ h.1 h.2; cases cs';
    case _ h =>
      have ηreflp := @refl_is_val Γ η A B dctx ηJ h;
      have ηrefl := ηreflp.1;
      subst ηrefl; apply Or.inr;
      have reds : ∃ t', Red Γ (t ▹ refl! A) t' := Exists.intro [t] Red.cast;
      apply reds;
    case _ h => cases h; case _ w h =>
      apply Or.inr
      generalize tlp : List.map (t ▹ ·) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (t ▹ η) t' := Exists.intro tl' (Red.cast_congr h tlp);
      apply reds;

case _ => apply Or.inl Val.refl
case sym Γ η A B ηJ ηs =>
  cases h; case _ w h =>
  have h2 := invert_eq_kind h.2; subst h2;
  have h2 := flip_eq h.2;
  simp at ηs; have ηs' := @ηs wΓ dctx ★ h.1 h2;
  cases ηs';
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
case seq η1J η2J η1s η2s =>
  simp_all; cases h; case _ w h =>
    have weqstr := invert_eq_kind h.2; subst weqstr;
    have η1s' := η1s ★ h.1;
    sorry
case appc Γ A K1 K2 B η1 C D η2 aK bK η1J cJ dJ η2J _ _ η1s _ _ η2s  =>
  -- check if η1 reduces or η2 reduces if both are values then reduce to refl
  simp_all; cases h; case _ w h =>
  have weqstr := invert_eq_kind h.2; subst weqstr;
  have lemA := classification_lemma aK; simp at lemA;
  cases lemA;
  case _ wA arrk1k2 =>
    have η1s' := η1s ★ h.1 (Judgment.eq arrk1k2 aK bK);
    cases η1s';
    case _ vη1 =>
      have η1refl := refl_is_val dctx η1J vη1;
      have aeqB := η1refl.2; have η1rfl := η1refl.1;
      -- subst aeqB; subst η1rfl; simp at *;
      have lemC := classification_lemma cJ; simp at lemC; cases lemC;
      case _ k1ki =>

        -- have eqCDstar := @invert_eq_kind Γ C D sorry;
        -- have η2s' := η2s ★ (Judgment.eq k1ki cJ dJ);
        sorry
      case _ hB =>
        cases hB;
        case _ k1ki =>
          have eqCDstar := @invert_eq_kind Γ C D ★;
          -- have η2s' := η2s ★ (Judgment.eq k1ki cJ dJ);
          sorry
        case _ h => cases h; case _ w h => sorry

    case _ h =>
      apply Or.inr; cases h; case _ w tl =>
      generalize tlp : List.map (· `@c η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `@c η2) t' := Exists.intro tl' (Red.appc_congr1 tl tlp);
      apply reds

  case _ wB hB => cases hB; case _ w h => cases h.2; case _ h => cases h.1

case arrowc => -- check if η1 reduces or η2 reduces if both are values then reduce to refl
  cases h; case _ w h =>
  cases h; case _ w h =>
    have keqstr := invert_eq_kind h; subst keqstr;
    have lem := classification_lemma h; simp at lem; cases lem;
    case _ h => sorry
    case _ h => sorry

case fst =>
  sorry
case snd η _ _ _ _ _ _ _ _ _ ηs =>
  simp_all; cases h; case _ w h =>
  have weqstr := invert_eq_kind h.2; subst weqstr;
  have ηs' := ηs ★ h.1;
  sorry
case _ K A B t allAJ allBJ _ _ _ ts =>
  -- cases h; case _ w h =>
  -- have weqstr := invert_eq_kind h.2; subst weqstr;
  -- simp at ts;
  -- cases h.2; case _ h =>
  --   have ts' := ts sorry (Judgment.wfkidctx ★ (Judgment.ax sorry) ; sorry
  cases h; case _ h =>
  cases h.2; cases h.1;
  have lem := classification_lemma h.2; simp at lem; cases lem;
  case _ allAJ' allBJ' _ _ =>
   have keq := uniqueness_of_types allAJ' allAJ; subst keq;
   sorry
  case _ h => cases h; case _ allAJ' allBJ' _ _ _ =>
   cases h.2; cases h.1; have keq := uniqueness_of_types allAJ' allAJ; subst keq;
   sorry

case _ Γ η1 K A B C D η2 _ _ η1J CKJ _ η2J _ _ η1s _ _ η2s =>
  simp_all; cases h; case _ w h =>
  have lem := classification_lemma η2J; simp at lem; cases lem;
  case _ h => cases h;
  case _ h => cases h; case _ w' h' =>
  have weqstar := invert_eq_kind h'.2; subst weqstar;
  cases h'.2; cases h'.1; have η2s' := @η2s ★ h'.1 h'.2;
  cases η2s';
  case _ h =>
    have η2refp := refl_is_val dctx η2J h;
    have η2refl := η2refp.1; -- subst ηrefl;
    have lem := classification_lemma η1J; simp at lem; cases lem;
    case _ h => cases h;
    case _ h => cases h; case _ K' _ CKJ' _ _ w' h' =>
    have kk' := uniqueness_of_types CKJ CKJ'; subst kk';
    have weqstar := invert_eq_kind h'.2; subst weqstar;
    cases h'.2; cases h'.1; have η1s' := @η1s ★ h'.1 h'.2;
    cases η1s';
    case _ h =>
      have η1refp := refl_is_val dctx η1J h;
      have η1refl := η1refp.1; -- subst ηrefl;
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
