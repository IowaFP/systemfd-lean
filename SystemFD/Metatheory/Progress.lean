
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


theorem invert_lamt_ty : Γ ⊢ Λ[A] b : Ty -> (.kind A :: Γ) ⊢ b : BTy -> Ty = ∀[ A ] BTy := by
intros ltyJ btyJ;
have lamtJ := Judgment.lamt sorry btyJ sorry;
apply uniqueness_of_types ltyJ lamtJ;

theorem opent_kind : ⊢ Γ -> Γ d@ x = .opent t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry

theorem lift_stable {Γ : Ctx Term} {n : Nat} : (Ctx.is_stable Γ n) -> ((Ctx.is_stable Γ n) = true) := by simp_all;

theorem neutral_form_shape : Val Γ t ->
        t.neutral_form = .some (n, ts)
        -> ¬ ((t = `λ[A] b)
            ∨ (t = Λ[A] b)
            ∨ (t = .letterm A t' b)
            ∨ t = .guard p s b
            ∨ t = .ite p s b c
            ∨ t = .kind
            ∨ t = .type
            ) := by
intros tnf; induction t;
any_goals (solve | simp_all)

theorem invert_eq_kind : Γ ⊢ (A ~ B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_arr_kind : Γ ⊢ (A -t> B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_all_kind : (Γ ⊢ ∀[ A ] B : w) -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

def DeclCtx (Γ : Ctx Term) : Prop := ∀ n, ¬ Γ.is_lam_bound n

theorem refl_is_val : DeclCtx Γ -> Γ ⊢ η : (A ~ B)
                    -> Val Γ η
                    -> η = refl! A ∧ A = B := by

intros dctx ηJ vη; induction vη;
case _ Γ t n _ _ n_stable =>
  have x_no_lam : ¬ Γ.is_lam_bound n := dctx n;
  unfold Ctx.is_stable at n_stable;
  unfold Frame.is_stable at n_stable;
  split at n_stable;
  any_goals (solve | simp_all);
  case _ =>
    unfold Ctx.is_lam_bound at x_no_lam; unfold Frame.is_lam_bound at x_no_lam;
    -- split at x_no_lam;
    cases t;
    any_goals (solve | simp_all)
    case _ a anf =>
      have anf' : ((#a).neutral_form = .some (a, [])) := @Term.var_neutral_form a;
      rw [anf'] at anf; injection anf with aeqs; simp_all;
      sorry;
    case _  =>  sorry

case _ => cases ηJ
case _ => cases ηJ
case _ => cases ηJ; simp_all


theorem invert_appk_val : Γ ⊢ t : (A -k> B)
                       -> Val Γ t -> t.neutral_form = .none
                       -> t = Λ[A] t' := by
intros tJ vt tnotnormal; induction vt;
case _ => simp_all
case _ => cases tJ
case _ => cases tJ
case _ => cases tJ

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
  case _ =>  -- classification lemma
    sorry
  case _ f t x_is_ctor =>
    have xx : Frame.is_stable (Γ d@ x) := by unfold Frame.is_stable; rw[x_is_ctor];
    have hh : (#x).neutral_form = .some (x, []) := Term.var_neutral_form;
    apply Or.inl (Val.app hh xx)
  case _ =>    -- classification lemma
    injection xTy with teqT; symm at teqT; subst teqT; cases h; case _ h =>
    sorry
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
  cases h; case _ w h =>
  simp at fs;
  have arrK : (Γ ⊢ (A -k> B) : .kind) := sorry;
  have fs' := @fs wΓ dctx w h.1 sorry;
  sorry

case _ => cases h; case _ h => cases h.2; cases h.1

case ite Γ p A s _ i _ _ e _ _ _ _ _ _ _ _ _ _ pJ sJ _ iJ _ eJ =>
  simp_all;
  have pJ' := pJ;
  sorry

case guard => sorry

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lam
case app Γ f A B a B' fJ aJ _ fs as =>
  simp_all; cases h; case _ w h =>
  have fs' := @fs w (h.1) sorry; have as' := @as w h.1 sorry;
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
      cases h; case _ A b l r =>
        sorry -- bogus case
    case refl => cases h; case _ xT wT h =>
      have reflT := Judgment.refl wT h;
      sorry -- bogus case
  case inr h => cases h; case _ w h => -- f steps
    generalize tlp : List.map (· `@ a) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (f `@ a) t' := Exists.intro tl' (Red.app_congr h tlp);
    apply Or.inr reds

case _ _ A t _ _ _ _ _ _ _ => apply Or.inl Val.lamt
case _ fJ aJ fs as =>
  simp_all; cases h; case _ w h =>
  sorry
case _ => sorry
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
case _ η1J η2J η1s η2s =>
  simp_all; cases h; case _ w h =>
    have weqstr := invert_eq_kind h.2; subst weqstr;
    have η1s' := η1s ★ h.1 sorry;
    sorry
case _ => sorry -- cases h; case _ h => cases h.2; cases h.1
case _ => -- bogus case
  cases h; case _ w h =>
  cases h; case _ w h =>
    have keqstr := invert_eq_kind h; subst keqstr;
    sorry
case _ =>
  sorry
case _ =>
  sorry
case _ => -- bogus case
  cases h; case _ h =>
  cases h.2; cases h.1;
  sorry
case _ η _ _ _ _ _ η' _ _ ηJ _ _ _ _ _ ηs _ _ _ =>
  simp_all; cases h; case _ h =>
  have eqKind := invert_eq_kind h.2;
  subst eqKind;
  have ηs' := @ηs ★ h.1 ;
  sorry








-- @[simp]
-- abbrev MaybeStep : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
-- | .prf => λ Γ => λ(t , A) => (∃ K, Γ ⊢ K : .kind ∧ Γ ⊢ A : K) ->  Neutral Γ t ∨ Val Γ t ∨ ∃ t', Red Γ t t'
-- | .wf  => λ _ => λ () => true

-- theorem progress_lemma : Judgment v Γ ix -> MaybeStep v Γ ix := by
-- intros j; induction j;
-- any_goals (solve | simp_all)
-- all_goals (intro h)
-- case _ Γ A t b _ _ _ _ _ _ _ ih _ =>
--   simp_all;
--   generalize tl' : [b β[ t ]] = t' at *; symm at tl';
--   have reds := @Red.letbeta Γ A t b; rw [<-tl']  at reds;
--   have ereds : ∃ t', Red Γ (.letterm A t b) t' := Exists.intro t' reds;
--   apply Or.inr (Or.inr ereds);
-- case _ => cases h; case _ w h => cases h.2;
--  -- VAR
-- case _ => sorry
-- case _ => cases h; case _ h => cases h.2
-- case _ => cases h; case _ h => cases h.2; sorry
-- case _ => cases h; case _ h => cases h.2; cases h.1
-- case _ => simp_all; sorry -- uses classification lemma
-- case _ => simp_all; sorry -- uses classification lemma

-- -- ITE
-- case _ Γ p _ s _ b _ _ c _ _ _ _ phead _ hmatch prefixmatch _ _ pih sih _ _ _ _ =>
--   simp at pih;
--   sorry
--   -- simp_all; cases pih;
--   -- case _ ph =>
--   --   cases phead; sorry
--   -- case _ ph =>
--   --   cases ph;
--   --   case _ ph =>
--   --     cases sih;
--   --     case _ h => apply Or.inl (Neutral.iteNe h)
--   --     case _ h =>
--   --     cases h;
--   --     case _ h =>
--   --       cases hmatch;
--   --       case refl x _ =>
--   --         cases x;
--   --         case _ =>
--   --         cases phead;
--   --         case _ pnf pJ => sorry
--   --       case _ x => sorry
--   --       case _ x => sorry
--   --     case _ h =>
--   --     cases h; case _ w h =>
--   --     generalize tlp' : List.map (Term.ite p · b c) w = tl' at *; symm at tlp';
--   --     have t' := Red.ite_congr h tlp';
--   --     apply Or.inr (Or.inr (Exists.intro tl' t'))
--   --   case _ ph =>
--   --   cases ph; case _ ts preds =>
--   --   cases phead; case _ w pctor =>
--   --     simp_all; have pctorstable := Frame.is_ctor_implies_is_stable (And.right pctor);
--   --     have pnf := And.left pctor; symm at pnf;
--   --     have pnoreds := stable_no_reduce pnf pctorstable;
--   --     have preds := Exists.intro ts preds; simp_all;
-- -- GUARD
-- case _ => sorry

-- case _ Γ A t _ _ _ _ _ _ _  =>
--   simp_all; have vlam : Val Γ (`λ[A] t) :=  (@Val.lam Γ A t); apply Or.inr (Or.inl vlam);
-- case _ => sorry
-- case _ Γ A t _ _ _ _ _ _ _ =>
--     simp_all; have vlam : Val Γ (Λ[A] t) :=  (@Val.lamt Γ A t); apply Or.inr (Or.inl vlam);
-- case _ => sorry
-- case _ ih => sorry

-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
