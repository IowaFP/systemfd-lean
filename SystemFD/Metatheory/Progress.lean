
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction

inductive Val : Ctx Term -> Term -> Prop where
| app : t.neutral_form = .some (n, ts)
      -> (Γ.is_stable_red n)
      -> Val Γ t
| lam :  Val Γ (`λ[a] b)
| lamt : Val Γ (Λ[A] b)
| refl : Val Γ (refl! _)
| star : Val Γ ★
| arr :  Val Γ (A -t> B)
| arrk : Val Γ (A -k> B)
| all : Val Γ (∀[A]B)
| eq : Val Γ (A ~ B)

theorem val_sound_var_lemma :
  t.neutral_form = .some (n, sp) ->
  Γ.is_stable_red n ->
  ∀ t', ¬ (Red Γ t t')
:= by
intro j1 j2 t' r
induction t generalizing n sp Γ t'
all_goals (try simp at j1)
case _ x =>
  cases j1; case _ e1 e2 =>
    subst e1; subst e2
    cases r
    case _ x' sp' tl q1 q2 q3 q4 =>
      replace q1 := Frame.is_openm_destruct q1
      cases q1; case _ q1 =>
        simp at *; cases q3; case _ e1 e2 =>
          subst e1; subst e2
          unfold Frame.is_stable_red at j2
          simp at j2; rw [q1] at j2; simp at j2
    case _ s x' sp' t q1 q2 =>
      simp at *; cases q2; case _ e1 e2 =>
        subst e1; subst e2
        rw [<-q1] at j2; unfold Frame.is_stable_red at j2
        simp at j2
case _ v t1 t2 ih1 ih2 =>
  cases v; all_goals (try simp at j1)
  case _ =>
    rw [Option.bind_eq_some] at j1; simp at j1
    cases j1; case _ a j1 =>
    cases j1; case _ b j1 =>
    cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; cases r <;> simp at *
      case _ x' sp' tl q1 q2 q3 q4 =>
        replace q3 := Eq.symm q3
        rw [Option.bind_eq_some] at q3; simp at q3
        cases q3; case _ u q3 =>
        cases q3; case _ v q3 =>
        cases q3; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          replace q1 := Frame.is_openm_destruct q1
          cases q1; case _ q1 =>
            rw [q1] at j2; unfold Frame.is_stable_red at j2
            simp at j2
      case _ s x sp' t q1 q2 =>
        replace q2 := Eq.symm q2
        rw [Option.bind_eq_some] at q2; simp at q2
        cases q2; case _ u q2 =>
        cases q2; case _ v q2 =>
        cases q2; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          rw [<-q1] at j2; unfold Frame.is_stable_red at j2
          simp at j2
  case _ =>
    rw [Option.bind_eq_some] at j1; simp at j1
    cases j1; case _ a j1 =>
    cases j1; case _ b j1 =>
    cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; cases r <;> simp at *
      case _ xx' sp' tl q1 q2 q3 q4 =>
        replace q3 := Eq.symm q3
        rw [Option.bind_eq_some] at q3; simp at q3
        cases q3; case _ u q3 =>
        cases q3; case _ v q3 =>
        cases q3; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          replace q1 := Frame.is_openm_destruct q1
          cases q1; case _ q1 =>
            rw [q1] at j2; unfold Frame.is_stable_red at j2
            simp at j2
      case _ s x sp' t q1 q2 =>
        replace q2 := Eq.symm q2
        rw [Option.bind_eq_some] at q2; simp at q2
        cases q2; case _ u q2 =>
        cases q2; case _ v q2 =>
        cases q2; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          rw [<-q1] at j2; unfold Frame.is_stable_red at j2
          simp at j2
      case _ tl r e => apply ih1 h1 j2 tl r
  case _ =>
    rw [Option.bind_eq_some] at j1; simp at j1
    cases j1; case _ a j1 =>
    cases j1; case _ b j1 =>
    cases j1; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; cases r <;> simp at *
      case _ x' sp' tl q1 q2 q3 q4 =>
        replace q3 := Eq.symm q3
        rw [Option.bind_eq_some] at q3; simp at q3
        cases q3; case _ u q3 =>
        cases q3; case _ v q3 =>
        cases q3; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          replace q1 := Frame.is_openm_destruct q1
          cases q1; case _ q1 =>
            rw [q1] at j2; unfold Frame.is_stable_red at j2
            simp at j2
      case _ s x sp' t q1 q2 =>
        replace q2 := Eq.symm q2
        rw [Option.bind_eq_some] at q2; simp at q2
        cases q2; case _ u q2 =>
        cases q2; case _ v q2 =>
        cases q2; case _ w1 w2 =>
        cases w2; case _ w2 w3 =>
          subst w2; rw [w1] at h1
          injection h1 with e
          injection e with e1 e2
          subst e1; subst e2
          rw [<-q1] at j2; unfold Frame.is_stable_red at j2
          simp at j2
      case _ tl r e => apply ih1 h1 j2 tl r

theorem val_sound : Val Γ t -> ∀ t', ¬ (Red Γ t t') := by
intro j; induction j
case _ Γ t n sp j2 j3 =>
  intro t' r
  apply val_sound_var_lemma j2 j3 t' r
all_goals (
  case _ =>
    intro t' r
    cases r <;> simp at *
)

theorem weaken_ctx_kind {Γ : Ctx Term}:
  (∀ x, Ctx.is_type Γ x = false) ->
  (∀ n, Ctx.is_type (.kind K :: Γ) n = false)
:= by
intro h n;
cases n;
case _ =>
  simp; unfold Frame.apply; simp
  unfold Frame.is_type; simp
case _ n => simp at *; rw [<-Frame.is_type_apply]; apply h n

theorem weaken_ctx_empty {Γ : Ctx Term}:
  (∀ x, Ctx.is_type Γ x = false) ->
  (∀ n, Ctx.is_type (.empty :: Γ) n = false)
:= by
intro h n;
cases n;
case _ =>
  simp; unfold Frame.apply; simp
  unfold Frame.is_type; simp
case _ n => simp at *; rw [<-Frame.is_type_apply]; apply h n

@[simp]
abbrev TypesAreValuesLemmaType : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , K) => Γ ⊢ K : .kind -> Val Γ t
| .wf  => λ _ => λ () => true

theorem types_are_values_lemma :
  Judgment v Γ ix ->
  TypesAreValuesLemmaType v Γ ix
:= by
intro j; induction j <;> simp at *
all_goals (intro h1)
case _ j _ _ _ _ =>
  have lem := uniqueness_of_types j h1
  injection lem
case _ => cases h1
case _ Γ x T j1 j2 _ =>
  generalize fdef : Γ d@ x = f at *
  have lem := frame_wf_by_index x j1
  rw [fdef] at lem
  cases lem
  all_goals (
    unfold Frame.get_type at j2
    simp at j2
  )
  case type j3 =>
    subst j2
    have lem := uniqueness_of_types h1 j3
    injection lem
  case openm j3 =>
    subst j2
    have lem := uniqueness_of_types h1 j3
    injection lem
  case term j3 _ =>
    subst j2
    have lem := uniqueness_of_types h1 j3
    injection lem
  all_goals (
    case _ =>
      subst j2; apply @Val.app Γ #x x []
      simp; simp; rw [fdef]; unfold Frame.is_stable_red
      simp
  )
case _ => cases h1
case _ => apply Val.all
case _ => apply Val.arr
case _ Γ f A B a j1 j2 ih1 ih2 =>
  have lem := classification_lemma j1 <;> simp at lem
  cases lem
  case _ lem =>
    replace ih1 := ih1 lem
    cases ih1
    case app x sp q1 q2 =>
      apply @Val.app Γ (f `@k a) x (sp ++ [(.kind, a)])
      simp; rw [Option.bind_eq_some]; simp; apply q2
      apply q1
    all_goals (cases j1)
  case _ lem =>
    cases lem; case _ K lem =>
      cases lem.2; cases lem.1
case _ => apply Val.eq
case _ j _ _ _ _ _ _ _ =>
  have lem := uniqueness_of_types j h1
  injection lem
case _ j _ _ _ _ _ =>
  have lem := uniqueness_of_types j h1
  injection lem
case _ => apply Val.lam
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  have lem := classification_lemma j1
  cases lem <;> simp at *
  case _ lem =>
    cases lem <;> simp at *
    case _ lem => cases lem
    case _ lem =>
      cases lem; case _ K lem =>
      cases lem.2; case _ j4 j5 =>
        replace j5 := beta_type j5 j2; simp at j5
        rw [j3] at h1
        have lem := uniqueness_of_types h1 j5
        injection lem
case _ => apply Val.lamt
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  have lem := classification_lemma j1
  cases lem <;> simp at *
  case _ lem =>
    cases lem <;> simp at *
    case _ lem => cases lem
    case _ lem =>
      cases lem; case _ K lem =>
      cases lem.2; case _ j4 j5 =>
        replace j5 := beta_kind j5 j2; simp at j5
        rw [j3] at h1
        have lem := uniqueness_of_types h1 j5
        injection lem
case _ j _ _ =>
  have lem := classification_lemma j <;> simp at lem
  cases lem
  case _ lem => cases lem
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ q _ j2 =>
      have lem2 := uniqueness_of_types h1 j2
      subst lem2; cases q
case _ => apply Val.refl
all_goals (case _ => cases h1)

theorem types_are_values :
  Γ ⊢ t : K ->
  Γ ⊢ K : .kind ->
  Val Γ t
:= by
intro j1 j2
apply types_are_values_lemma j1 j2

theorem refl_var_spine_lemma :
  Γ.is_stable_red n ->
  Γ ⊢ (#n).apply_spine sp : (A ~ B) ->
  False
:= by
intro j1 j2
have lem := inversion_apply_spine j2
cases lem; case _ C lem =>
cases lem; case _ h1 h2 =>
cases h2; case _ j3 j4 =>
  have lem := classification_lemma j2 <;> simp at lem
  cases lem
  case _ lem => cases lem
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ q1 q2 q3 =>
      apply ctx_get_var_no_spine_eq_type j3 j1
      rw [j4]; apply lem.2; apply h1

theorem refl_is_val :
  Γ ⊢ η : (A ~ B) ->
  Val Γ η ->
  η = refl! A ∧ A = B
:= by
intros ηJ vη; induction vη;
any_goals(solve | cases ηJ)
case _ Γ t n ts tnf n_stable =>
     symm at tnf; replace tnf := Term.neutral_form_law tnf;
     subst tnf;
     exfalso;
     apply (refl_var_spine_lemma n_stable ηJ);
case _ => cases ηJ; case _ fJ =>
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h; case _ h => cases h
  case _ h => apply And.intro rfl rfl

@[simp]
abbrev ProgressLemmaType : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , _) => Val Γ t ∨ ∃ t', Red Γ t t'
| .wf  => λ _ => λ () => true

theorem progress_lemma :
  (∀ x, ¬ Γ.is_type x) ->
  Judgment v Γ ix ->
  ProgressLemmaType v Γ ix
:= by
intro h1 j
induction j <;> try simp at *
case _ =>
  apply Or.inr; apply Exists.intro _
  apply Red.letbeta
case _ => apply Or.inl; apply Val.star
case _ Γ x T j1 j2 _ =>
  generalize fdef : Γ d@ x = f at *
  cases f
  case term A t =>
    apply Or.inr; apply Exists.intro _
    apply @Red.letterm A #x x [] Γ t
    simp; rw [fdef]
  case openm A =>
    let insts := get_instances Γ x
    apply Or.inr; apply Exists.intro insts
    apply @Red.inst #x x [] insts Γ insts
    simp; simp; rw [fdef]; unfold Frame.is_openm; simp
    simp; simp
  case type =>
    replace h1 := h1 x
    rw [fdef] at h1; unfold Frame.is_type at h1
    simp at h1
  case empty =>
    unfold Frame.get_type at j2; simp at j2
  all_goals (
    apply Or.inl; apply @Val.app Γ #x x []
    simp; simp; unfold Frame.is_stable_red
    rw [fdef]
  )
case _ => apply Or.inl; apply Val.arrk
case _ => apply Or.inl; apply Val.all
case _ => apply Or.inl; apply Val.arr
case _ Γ f A B a j1 j2 ih1 ih2 =>
  have lem := classification_lemma j1; simp at lem
  cases lem
  case _ lem =>
    have lem2 := types_are_values j1 lem
    cases lem2
    case app x sp q1 q2 =>
      apply Or.inl; apply @Val.app Γ (f `@k a) x (sp ++ [(.kind, a)])
      simp; rw [Option.bind_eq_some]; simp; apply q2
      apply q1
    all_goals (cases j1)
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; cases lem.1
case _ => apply Or.inl; apply Val.eq
case _ Γ p A s R i B T e j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
  replace ih2 := ih2 h1
  cases ih2
  case _ h2 =>
    apply Or.inr
    unfold ValidHeadVariable at j5
    unfold ValidHeadVariable at j6
    cases j5; case _ w1 j5 =>
    cases w1; case _ w1 sp1 =>
    cases j6; case _ w2 j6 =>
    cases w2; case _ w2 sp2 =>
      simp at j5; simp at j6
      cases h2
      case _ x sp3 q2 q3 =>
        generalize tstdef : prefix_equal sp1 sp3 = tst
        cases tst
        case _ =>
          apply Exists.intro _
          apply Red.ite_missed j5.1 (Eq.symm q3) q2 (Or.inr tstdef)
        case _ ξ =>
          cases (Nat.decEq w1 x)
          case _ h =>
            apply Exists.intro _
            apply Red.ite_missed j5.1 (Eq.symm q3) q2 (Or.inl h)
          case _ h =>
            subst h; apply Exists.intro _
            apply Red.ite_matched j5.1 (Eq.symm q3) (Eq.symm tstdef) j5.2
      all_goals (cases j2; simp at j6)
  case _ h2 =>
    cases h2; case _ s' h2 =>
      apply Or.inr
      apply Exists.intro (List.map (fun x => p.ite x i e) s')
      apply Red.ite_congr h2; rfl
case _ Γ p A s R t B T j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
  replace ih2 := ih2 h1
  cases ih2
  case _ h2 =>
    apply Or.inr
    unfold ValidHeadVariable at j5
    unfold ValidHeadVariable at j6
    cases j5; case _ w1 j5 =>
    cases w1; case _ w1 sp1 =>
    cases j6; case _ w2 j6 =>
    cases w2; case _ w2 sp2 =>
      simp at j5; simp at j6
      cases h2
      case _ x sp3 q2 q3 =>
        generalize tstdef : prefix_equal sp1 sp3 = tst
        cases tst
        case _ =>
          apply Exists.intro _
          apply Red.guard_missed j5.1 (Eq.symm q3) q2 (Or.inr tstdef)
        case _ ξ =>
          cases (Nat.decEq w1 x)
          case _ h =>
            apply Exists.intro _
            apply Red.guard_missed j5.1 (Eq.symm q3) q2 (Or.inl h)
          case _ h =>
            subst h; apply Exists.intro [t.apply_spine ξ]
            apply @Red.guard_matched p w1 sp1 s sp3 ξ Γ t
            apply j5.1; apply Eq.symm q3
            apply Eq.symm tstdef
      all_goals (cases j2; simp at j6)
  case _ h2 =>
    cases h2; case _ s' h2 =>
      apply Or.inr
      apply Exists.intro (List.map (fun x => p.guard x t) s')
      apply Red.guard_congr h2; rfl
case _ => apply Or.inl; apply Val.lam
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  replace ih1 := ih1 h1
  cases ih1
  case _ h2 =>
    cases h2
    case app x sp q1 q2 =>
      apply Or.inl; apply @Val.app Γ (f `@ a) x (sp ++ [(.term, a)])
      simp; rw [Option.bind_eq_some]; simp; apply q2
      apply q1
    case lam =>
      apply Or.inr; apply Exists.intro _
      apply Red.beta
    all_goals (cases j1)
  case _ h2 =>
    cases h2; case _ f' h2 =>
      apply Or.inr; apply Exists.intro (List.map (· `@ a) f')
      apply Red.app_congr h2 rfl
case _ => apply Or.inl; apply Val.lamt
case _ Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  replace ih1 := ih1 h1
  cases ih1
  case _ h2 =>
    cases h2
    case app x sp q1 q2 =>
      apply Or.inl; apply @Val.app Γ (f `@t a) x (sp ++ [(.type, a)])
      simp; rw [Option.bind_eq_some]; simp; apply q2
      apply q1
    case lamt =>
      apply Or.inr; apply Exists.intro _
      apply Red.betat
    all_goals (cases j1)
  case _ h2 =>
    cases h2; case _ f' h2 =>
      apply Or.inr; apply Exists.intro (List.map (· `@t a) f')
      apply Red.appt_congr h2 rfl
case _ Γ t A c B j1 j2 ih1 ih2 =>
  apply Or.inr
  replace ih2 := ih2 h1
  cases ih2
  case _ h2 =>
    have lem := refl_is_val j2 h2
    cases lem; case _ e1 e2 =>
      subst e1; subst e2
      apply Exists.intro _
      apply Red.cast
  case _ h2 =>
    cases h2; case _ c' h2 =>
      apply Exists.intro (List.map (t ▹ ·) c')
      apply Red.cast_congr h2 rfl
case _ => apply Or.inl; apply Val.refl
case sym Γ η A B ηJ ηs =>
  apply Or.inr
  cases ηs h1;
  case _ h =>
    have x := refl_is_val ηJ h;
    have xeqrefl := x.left;
    have aeqB := x.right; subst xeqrefl;
    have reds : ∃ t', Red Γ (sym! refl! A) t' := Exists.intro [refl! A] (@Red.sym Γ A);
    apply reds;
  case _ ηreds => cases ηreds; case _ w h =>
    generalize tlp : List.map (sym! ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (sym! η) t' := Exists.intro tl' (Red.sym_congr h tlp);
    apply reds;

case seq Γ η1 A B η2 C η1J η2J η1s η2s =>
  apply Or.inr; cases (η2s h1);
  case _ h =>
    have η2refp := refl_is_val η2J h;
    have η2refl := η2refp.1; cases (η1s h1);
    case _ h =>
      have η1refp := refl_is_val η1J h;
      have η1refl := η1refp.1; have aeqB := η1refp.2; have BeqC := η2refp.2
      subst η1refl; subst η2refl; subst aeqB;
      have reds : ∃ t', Red Γ ((refl! A) `; (refl! A)) t' := Exists.intro [refl! A] Red.seq;
      apply reds;
    case _ h => cases h; case _ w h =>
      generalize tlp : List.map (· `; η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `; η2) t' := Exists.intro tl' (Red.seq_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    generalize tlp : List.map (η1 `; ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `; η2) t' := Exists.intro tl' (Red.seq_congr2 h tlp);
    apply reds

case appc Γ A K1 K2 B η1 C D η2 aK bK η1J cJ dJ η2J _ _ η1s _ _ η2s  =>
  apply Or.inr;
  cases (η2s h1);
  case _ h =>
    have η2refp := refl_is_val η2J h;
    have η2refl := η2refp.1; cases (η1s h1);
    case _ h =>
      have η1refp := refl_is_val η1J h;
      have η1refl := η1refp.1;
      subst η1refl; subst η2refl;
      have reds : ∃ t', Red Γ ((refl! A) `@c (refl! C)) t' := Exists.intro [refl! (A `@k C)] Red.appc;
      apply reds
    case _ h => cases h; case _ w h =>
      generalize tlp : List.map (· `@c η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `@c η2) t' := Exists.intro tl' (Red.appc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    generalize tlp : List.map (η1 `@c ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `@c η2) t' := Exists.intro tl' (Red.appc_congr2 h tlp);
    apply reds


case arrowc Γ A B η1 C D η2 _ _ η1J _ _ η2J _ _ η1s _ _ η2s =>
  apply Or.inr; cases η2s (weaken_ctx_empty h1)
  case _ h =>
    have η2refp := refl_is_val η2J h;
    have η2refl := η2refp.1; cases (η1s h1);
    case _ h =>
      have η1refp := refl_is_val η1J h;
      have η1refl := η1refp.1;
      subst η1refl; subst η2refl;
      have reds : ∃ t', Red Γ (refl!(A) -c> refl! C) t' := Exists.intro [(refl! (A -t> C))] Red.arrowc;
      apply reds
    case _ h => cases h; case _ w h =>
      generalize tlp : List.map (· -c> η2) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 -c> η2) t' := Exists.intro tl' (Red.arrowc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    generalize tlp : List.map (η1 -c> ·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 -c> η2) t' := Exists.intro tl' (Red.arrowc_congr2 h tlp);
    apply reds

case fst Γ A _ _ _ η C _ _ _ ηJ _ _ ηs =>
  apply Or.inr; cases (ηs h1);
  case inl h =>
    have ηrp := refl_is_val ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    have reds : ∃ t', Red Γ ((refl! (A `@k C)).!1) t' := Exists.intro [refl! A] Red.fst;
    apply reds;
  case inr h => cases h; case _ w h =>
    generalize tlp : List.map (·.!1) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η.!1) t' := Exists.intro tl' (Red.fst_congr h tlp);
    apply reds

case snd Γ _ C _ η A _ _ _ _ ηJ _ _ _ ηs =>
  apply Or.inr;
  cases (ηs h1);
  case inl h =>
    have ηrp := refl_is_val ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    have reds : ∃ t', Red Γ ((refl! (A `@k C)).!2) t' := Exists.intro [refl! C] Red.snd;
    apply reds;
  case inr h => cases h; case _ w h =>
    generalize tlp : List.map (·.!2) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η.!2) t' := Exists.intro tl' (Red.snd_congr h tlp);
    apply reds

case _ Γ K A B η allAJ allBJ ηJ _ _ ts =>
  cases allAJ; case _ kkind _ =>
  have ts' : Val (Frame.kind K :: Γ) η ∨ ∃ t', Red (Frame.kind K :: Γ) η t' := ts (weaken_ctx_kind h1)
  apply Or.inr;
  cases ts';
  case inr h => cases h; case _ w h =>
    generalize tlp : List.map (∀c[K]·) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (∀c[K] η) t' := Exists.intro tl' (Red.allc_congr h tlp);
    apply reds
  case inl h =>
    have ηrp := refl_is_val ηJ h; have ηrfl := ηrp.1; subst ηrfl;
    have reds : ∃ t', Red Γ ((∀c[K] refl! A)) t' := Exists.intro [refl! (∀[K]A)] Red.allc;
    apply reds;

case _ Γ η1 K A B C D η2 _ _ η1J CKJ _ η2J _ _ η1s _ _ η2s =>
  apply Or.inr;
  cases (η2s h1);
  case _ h =>
    have η2refp := refl_is_val η2J h;
    have η2refl := η2refp.1; cases (η1s h1);
    case _ h =>
      have η1refp := refl_is_val η1J h;
      have η1refl := η1refp.1;
      subst η1refl; subst η2refl;
      have reds : ∃ t', Red Γ (refl!(∀[K] A) `@c[refl! C]) t' := Exists.intro [refl! (A β[ C ])] Red.apptc;
      apply reds
    case _ h => cases h; case _ w h =>
      generalize tlp : List.map (· `@c[η2]) w = tl' at *; symm at tlp;
      have reds : ∃ t', Red Γ (η1 `@c[η2]) t' := Exists.intro tl' (Red.apptc_congr1 h tlp);
      apply reds
  case _ h => cases h; case _ w h =>
    generalize tlp : List.map (η1 `@c[·]) w = tl' at *; symm at tlp;
    have reds : ∃ t', Red Γ (η1 `@c[η2]) t' := Exists.intro tl' (Red.apptc_congr2 h tlp);
    apply reds

theorem progress :
  (∀ x, ¬ Γ.is_type x) ->
  Γ ⊢ t : A ->
  Val Γ t ∨ (∃ t', Red Γ t t')
:= by
intro h j
apply progress_lemma h j
