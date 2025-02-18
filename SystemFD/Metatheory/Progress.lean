
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
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

  | letdata : Neutral (.datatype t' :: Γ) t -> Neutral Γ (.letdata t' t)
  | letterm : Neutral (.term A t' :: Γ) t -> Neutral Γ (.letterm A t' t)
  | insttype : Neutral (.inst A t' :: Γ) t -> Neutral Γ (.inst A t' t)
  | letctor : Neutral (.ctor t' :: Γ) t -> Neutral Γ (letctor! t' t)
  | letopen : Neutral (.openm t' :: Γ) t -> Neutral Γ (letopen! t' t)
  | letopentype : Neutral (.opent t' :: Γ) t -> Neutral Γ (letopentype! t' t)
  | letinsttype : Neutral (.insttype t' :: Γ) t -> Neutral Γ (insttype! t' t)
  | letinst : Neutral (.inst n t' :: Γ) t -> Neutral Γ (.inst n t' t)


inductive Val : Ctx Term -> Term -> Prop where
  | app : t.neutral_form = .some (n, ts)
        -> Γ.is_stable n
        -> Val Γ t
  | lam :  Val Γ (`λ[a] b)
  | lamt : Val Γ (Λ[A] b)
  | refl : Val Γ (refl! _)
  | letdata : Val (.datatype t' :: Γ) t -> Val Γ (.letdata t' t)
  | letterm : Val (.term A t' :: Γ) t -> Val Γ (.letterm A t' t)
  | insttype : Val (.inst A t' :: Γ) t -> Val Γ (.inst A t' t)
  | letctor : Val (.ctor t' :: Γ) t -> Val Γ (letctor! t' t)
  | letopen : Val (.openm t' :: Γ) t -> Val Γ (letopen! t' t)
  | letopentype : Val (.opent t' :: Γ) t -> Val Γ (letopentype! t' t)
  | letinsttype : Val (.insttype t' :: Γ) t -> Val Γ (insttype! t' t)
  | letinst : Val (.inst n t' :: Γ) t -> Val Γ (.inst n t' t)

theorem flip_eq : Γ ⊢ (A ~ B) : ★ -> Γ ⊢ (B ~ A) : ★ := by
intros h; cases h; case _ AJ BJ => apply Judgment.eq BJ AJ

theorem var_neutral_form : (#n).neutral_form = .some (n, []) := by simp_all

theorem lift_stable {Γ : Ctx Term} {n : Nat} : (Ctx.is_stable Γ n) -> ((Ctx.is_stable Γ n) = true) := by simp_all;

theorem refl_is_val : Γ ⊢ η : (A ~ B) -> Val Γ η -> η = refl! A ∧ A = B := by
intros ηJ vη;
 sorry

theorem invert_appk_val : Γ ⊢ t : (A -k> B) -> Val Γ t -> ∃ t', (.kind A :: Γ) ⊢ t' : B ∧ t = Λ[A] t' := by
intros tJ vt; induction vt;
case _ => sorry
case _ => simp_all; contradiction;
case _ => simp_all; cases tJ;
case _ => simp_all; contradiction;
case _ ih =>  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry


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

theorem letterm_no_stable : Term.is_letterm Γ n = true -> ¬ Ctx.is_stable Γ n := by
intros lt; simp_all; split at lt;
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
  case _ om _ _ _ =>
    have no_stable := openm_no_stable om; simp at no_stable; simp_all;
  case _ idx =>
    symm at idx; have lt := Term.id_is_letterm idx;
    have no_stable := letterm_no_stable lt; simp at no_stable; simp_all;
  case _ f _ _ _ _ _ nosome =>
    simp_all; rw[Option.bind_eq_some] at tnf;
    cases tnf; case _ h =>
      simp_all; have wfst := And.left (And.right h);
      have wsnd := And.right (And.right h);
      sorry
  case _ =>
    simp_all; rw[Option.bind_eq_some] at tnf;
    cases tnf; case _ h =>
    simp_all; sorry
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
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
  case _ => simp_all
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
case _ => simp_all
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letdata h)
  case _ T _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letdata h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (T.letdata ·) w = tl' at *; symm at tlp';
      have t' := (Red.letdata_congr h tlp');
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letctor h)
  case _ T _ _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letctor h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (letctor! T ·) w = tl' at *; symm at tlp';
      have t' := Red.letctor_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letopentype h)
  case _ T _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letopentype h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (letopentype! T ·) w = tl' at *; symm at tlp';
      have t' := Red.letopentype_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letopen h)
  case _ T _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letopen h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (letopen! T ·) w = tl' at *; symm at tlp';
      have t' := Red.letopen_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letinsttype h)
  case _ T _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letinsttype h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (insttype! T ·) w = tl' at *; symm at tlp';
      have t' := Red.insttype_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letinst h)
  case _ n _ t _ _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letinst h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (λ x => Term.inst n t x) w = tl' at *; symm at tlp';
      have t' := Red.inst_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'));
case _ ih =>
  simp_all; cases ih;
  case _ h => apply Or.inl (Neutral.letterm h)
  case _ A t _ _ _ _ _ _ _ h =>
    cases h;
    case _ h => apply Or.inr (Or.inl (Val.letterm h))
    case _ h =>
      cases h; case _ w h =>
      generalize tlp' : List.map (Term.letterm A t ·) w = tl' at *; symm at tlp';
      have t' := Red.letterm_congr h tlp';
      apply Or.inr (Or.inr (Exists.intro tl' t'))

case _ ih =>
  simp_all; sorry -- classification lemma
case _ n _ _ _ _ =>
  -- simp_all; match Γ.is_stable n with
  -- | true =>
  --   have hh : Γ.is_stable n = true := by simp_all;
  --   have appp := Val.app var_neutral_form hh;
  --   constructor;  sorry
  -- | false =>
  sorry
case _ => simp_all; sorry -- uses classification lemma?
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
case _ ih =>
  simp_all;
  cases ih;
  case _ => sorry
  case _ => sorry

case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry

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
