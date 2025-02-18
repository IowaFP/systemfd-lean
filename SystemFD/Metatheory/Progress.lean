
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

theorem var_neutral_form : (#n).neutral_form = .some (n, []) := by simp_all

theorem lift_stable {Γ : Ctx Term} {n : Nat} : (Ctx.is_stable Γ n) -> ((Ctx.is_stable Γ n) = true) := by simp_all;

theorem refl_is_val : Γ ⊢ η : (A ~ B) -> Val Γ η -> η = refl! A ∧ A = B := by
intros ηJ vη; induction vη;
case _ => simp_all; sorry
case _ => cases ηJ
case _ => cases ηJ
case _ => cases ηJ; simp_all


theorem invert_appk_val : Γ ⊢ t : (A -k> B) -> Val Γ t -> ∃ t', (.kind A :: Γ) ⊢ t' : B ∧ t = Λ[A] t' := by
intros tJ vt; induction vt;
case _ => simp_all;  sorry
case _ => cases tJ
case _ => cases tJ
case _ => cases tJ


theorem unique_neutral_form : (Term.neutral_form t = .some (n, sp)) -> (Term.neutral_form t = .some (n', sp')) -> (n = n') := by
intros tnf tnf';
induction t using Term.neutral_form.induct;
case _ => simp_all;
case _ => simp_all;
case _ => simp_all;
case _ => simp_all;
case _ => simp_all

theorem openm_no_stable : Term.is_openmethod Γ n = true -> ¬ Ctx.is_stable Γ n := by
intros om; simp_all; split at om;
case _ => unfold Frame.is_stable; simp_all
case _ => simp_all

theorem stable_no_reduce : t.neutral_form = .some (n, sp) -> Γ.is_stable n = true -> ¬ ∃ t', Red Γ t t' := by
intros tnf nstable x; cases x;
  case _ w h =>
  simp_all; induction h;
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ om _ _ _ => sorry
  case _ idx => sorry
  case _ f _ _ _ _ _ nosome =>
    simp_all; rw[Option.bind_eq_some] at tnf;
    cases tnf; case _ h =>
      simp_all; have wfst := And.left (And.right h);
      have wsnd := And.right (And.right h);
      sorry
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all

theorem val_no_red : Val Γ t -> ¬ ∃ t', Red Γ t t' := by
intros vt tred; induction vt;
case _ =>
  cases tred; case _ nf st w h =>
    have no_red := stable_no_reduce nf st;
    have reds := Exists.intro w h; simp_all;
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all
case _ => cases tred; case _ h =>
  cases h;
  case _ => simp_all

@[simp]
abbrev MaybeStep : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , _) => Neutral Γ t ∨ Val Γ t ∨ ∃ t', Red Γ t t'
| .wf  => λ _ => λ () => true

theorem progress_lemma : Judgment v Γ ix -> MaybeStep v Γ ix := by
intros j; induction j;
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all
case _ => simp_all

case _ ih =>
  simp_all; cases ih;
  case _ h => sorry -- apply Or.inr (Or.inr Red.letterm);
  case _ => sorry -- apply Or.inr (Or.inr Red.letterm);
case _ =>
  simp; sorry -- uses classification lemma?
case _ => simp_all; sorry -- uses classification lemma?
case _ => simp_all; sorry -- uses classification lemma?
case _ ih _ =>
  simp_all; cases ih;
  case _ => sorry
  case _ h =>
  cases h;
  case _ => sorry
  case _ => sorry
case _ => simp_all; sorry -- uses classification lemma
case _ => simp_all; sorry -- uses classification lemma
case _ => simp_all; sorry -- uses classification lemma
case _ p _ s _ b _ _ c _ _ _ _ phead _ hmatch prefixmatch _ _ pih sih _ _ _ _ =>
  simp_all; cases pih;
  case _ ph => sorry
  case _ ph =>
    cases ph;
    case _ ph =>
      cases sih;
      case _ h => apply Or.inl (Neutral.iteNe h)
      case _ h =>
      cases h;
      case _ h =>
        cases hmatch;
        case refl x _ =>
          cases x;
          case _ =>
          cases phead;
          case _ pnf pJ => sorry
        case _ x => sorry
        case _ x => sorry
      case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (Term.ite p · b c) w = tl' at *; symm at tlp';
      have t' := Red.ite_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'))
    case _ ph =>
    cases ph; case _ ts preds =>
    cases phead; case _ w pctor =>
      simp_all; have pctorstable := Frame.is_ctor_implies_is_stable (And.right pctor);
      have pnf := And.left pctor; symm at pnf;
      have pnoreds := stable_no_reduce pnf pctorstable;
      have preds := Exists.intro ts preds; simp_all;
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ ih =>  simp_all; sorry

case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry
case _ => simp_all; sorry

-- theorem progress_νT :
--     (Γ ⊢ A : ★) -> (Γ ⊢ t : A)
-- --------------------------------------
--   -> Val Γ t ∨ ∃ t', Red Γ t t' := by
-- intros Astar typingJ;
-- cases typingJ;
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ => cases Astar
-- case _ n _  aTy =>
--   unfold Frame.get_type at aTy;
--   cases Γ d@ n;
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   -- match Γ d@ n with
--   -- | .empty =>  at aTy; simp at aTy;  sorry
--   -- | .kind _ => sorry
--   -- | .type _ => sorry
--   -- | .datatype _ => sorry
--   -- | .ctor _ => sorry
--   -- | .opent _ => sorry
--   -- | .openm _ => sorry
--   -- | .insttype _ => sorry
--   -- | .inst _ _ => sorry
--   -- | .term _ _ => sorry

-- case _ => cases Astar
-- case _ => sorry -- proof by classification lemma
-- case _ => cases Astar
-- case _ f _ _ aty arrk => sorry -- proof by classification lemma
-- case _ => cases Astar
-- case _ => sorry
-- -- case _ p _ s _ i _ _ _ e _ _ pJ sJ Rstar cJ _ _ _ _ eJ => sorry
--   -- cases progress_νT Rstar sJ;
--   -- case _ νs => apply Or.inl (.iteNe νs)
--   -- case _ h => cases h; case _ w r =>
--   --   generalize tlp' : List.map (Term.ite p · i e) w = tl' at *; symm at tlp';
--   --   have t' := Red.ite_congr r tlp';
--   --   apply (Or.inr (Exists.intro tl' t'))
-- case _ p _ s _ t _ pJ sJ Rstar _ _ _ _ => sorry
--   -- cases progress_νT Rstar sJ;
--   -- case _ νs => apply (Or.inl (.guardNe νs))
--   -- case _ h => cases h; case _ w r =>
--   -- generalize tlp' : List.map (Term.guard p · t) w = tl' at *; symm at tlp';
--   -- have t' := Red.guard_congr r tlp';
--   -- apply (Or.inr (Exists.intro tl' t'))
-- case _ => apply Or.inl .lam
-- case _ f A B a fJ aJ _ => sorry
--   -- have arrStar : (Γ ⊢ (A -t> B) : ★) := .arrow sorry sorry;
--   -- cases (progress_νT arrStar fJ);
--   -- case _ h => apply Or.inl (.appNe h)
--   -- case _ h => cases h; case _ w r =>
--   -- generalize tlp' : List.map ( · `@ a) w = tl' at *; symm at tlp';
--   -- have t' := Red.app_congr r tlp';
--   -- apply (Or.inr (Exists.intro tl' t'))
-- case _ => apply Or.inl .lamt
-- case _ f A B a fJ aJ _ => sorry
-- --   have allStar : (Γ ⊢ (∀[A] B) : ★) := .allt sorry sorry sorry;
-- --   cases (progress_νT allStar fJ);
-- --   case _ h => apply Or.inl (.apptNe h)
-- --   case _ h => cases h; case _ w r =>
-- --   generalize tlp' : List.map ( · `@t a) w = tl' at *; symm at tlp';
-- --   have t' := Red.appt_congr r tlp';
-- --   apply (Or.inr (Exists.intro tl' t'))
-- case _ t B η tJ ηJ => sorry
--   -- have eqStar : (Γ ⊢ (B ~ A) : ★) := .eq sorry Astar;
--   -- cases (progress_νT eqStar  ηJ);
--   -- case _ h => apply (Or.inl (.castNe h))
--   -- case _ h => cases h; case _ w r =>
--   -- generalize tlp' : List.map (t ▹ ·) w = tl' at *; symm at tlp';
--   -- have t' := Red.cast_congr r tlp';
--   -- apply (Or.inr (Exists.intro tl' t'))
-- case _ => apply Or.inl .refl
-- case _ η A B ηJ => sorry
--   -- have eqStar : (Γ ⊢ (A ~ B) : ★) := flip_eq Astar;
--   -- cases progress_νT eqStar ηJ;
--   -- case _ h => apply Or.inl (.symNe h)
--   -- case _ h => cases h; case _ w r =>
--   -- generalize tlp' : List.map (sym! ·) w = tl' at *; symm at tlp';
--   -- have t' := Red.sym_congr r tlp';
--   -- apply (Or.inr (Exists.intro tl' t'))
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
