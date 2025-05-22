
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity

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
  have lem1 := kind_shape h1 rfl
  have lem2 := type_shape j (by constructor)
  exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
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
    have lem1 := kind_shape h1 rfl
    have lem2 := type_shape j3 (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case openm j3 =>
    subst j2
    have lem1 := kind_shape h1 rfl
    have lem2 := type_shape j3 (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case term j3 _ =>
    subst j2
    have lem1 := kind_shape h1 rfl
    have lem2 := type_shape j3 (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
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
    case choice =>
      cases j1; case _ h1 h2 _ _ =>
        cases h2; cases h1
    all_goals (cases j1)
  case _ lem =>
    cases lem; case _ K lem =>
      cases lem.2; cases lem.1
case _ => apply Val.eq
case _ j _ _ _ _ _ _ _ =>
  have lem1 := kind_shape h1 rfl
  have lem2 := type_shape j (by constructor)
  exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
case _ j _ _ _ _ _ =>
  have lem1 := kind_shape h1 rfl
  have lem2 := type_shape j (by constructor)
  exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
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
        replace j5 := beta_empty a j5;  simp at j5
        rw [j3] at h1
        have lem1 := kind_shape h1 rfl
        have lem2 := type_shape j5 (by constructor)
        exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
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
        have lem1 := kind_shape h1 rfl
        have lem2 := type_shape j5 (by constructor)
        exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
case _ j _ _ =>
  have lem := classification_lemma j <;> simp at lem
  cases lem
  case _ lem => cases lem
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ q _ j2 =>
      have lem2 := kind_shape h1 rfl
      have lem3 := uniqueness_of_super_kind lem2 h1 j2
      subst lem3; cases q
case _ => apply Val.refl
case empty j1 j2 _ _ =>
  have lem1 := kind_shape h1 rfl
  have lem2 := uniqueness_of_super_kind lem1 j2 h1
  subst lem2; cases j1
case choice ih1 ih2 => apply Val.choice (ih1 h1) (ih2 h1)
all_goals (try solve | case _ => cases h1)

theorem types_are_values :
  Γ ⊢ t : K ->
  Γ ⊢ K : □ ->
  Val Γ t
:= by
intro j1 j2
apply types_are_values_lemma j1 j2

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
case _ v _ _ ih1 ih2 =>
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

theorem val_sound : Val Γ t -> t ≠ `0 ∧ ∀ t', ¬ (Red Γ t t') := by
intro j; induction j
case app s x sp j1 j2 =>
  apply And.intro
  intro h; subst h; cases j1
  apply val_sound_var_lemma j1 j2
all_goals (
  case _ =>
    apply And.intro; simp
    intro t' r
    cases r <;> simp at *
    try case ctor2_congr1 ih1 ih2 _ r _ =>
      cases ih1; case _ h1 h2 =>
      apply h2 _ r
    try case ctor2_congr2 ih1 ih2 _ r _ =>
      cases ih2; case _ h1 h2 =>
      apply h2 _ r
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
abbrev ProgressLemmaType : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , _) => Val Γ t ∨ (∃ t', Red Γ t t') ∨ (t = `0)
| .wf  => λ _ => λ () => true

theorem progress_lemma :
  (∀ x, ¬ Γ.is_type x) ->
  Judgment v Γ ix ->
  ProgressLemmaType v Γ ix
:= by
intro h1 j
induction j <;> simp at *
case letterm =>
  apply Or.inr; apply Exists.intro _
  apply Red.letbeta
case ax => apply Or.inl; apply Val.star
case var Γ x T j1 j2 _ =>
  generalize fdef : Γ d@ x = f at *
  cases f
  case term A t =>
    apply Or.inr; apply Exists.intro _
    apply @Red.letterm A #x x [] Γ t
    simp; rw [fdef]
  case openm A =>
    generalize tldef : get_instances Γ x = tl at *
    generalize tdef : List.foldl (·⊕·) `0 tl = t at *
    apply Or.inr; apply Exists.intro t
    apply @Red.inst _ x [] tl _ tl t; simp
    unfold Ctx.is_openm; rw [fdef]
    unfold Frame.is_openm; simp; rw [tldef]
    simp; rw [tdef]
  case type =>
    replace h1 := h1 x; rw [fdef] at h1;
    unfold Frame.is_type at h1; simp at h1
  case empty =>
    unfold Frame.get_type at j2; simp at j2
  all_goals (
    apply Or.inl; apply @Val.app Γ #x x []
    simp; simp; unfold Frame.is_stable_red
    rw [fdef]
  )
case allk => apply Or.inl; apply Val.arrk
case allt => apply Or.inl; apply Val.all
case arrow => apply Or.inl; apply Val.arr
case appk j1 j2 ih1 ih2 =>
  have lem1 := classification_lemma j1; simp at lem1
  cases lem1
  case _ lem1 =>
    cases lem1; case _ lem1 lem2 =>
    have lem3 := Judgment.appk j1 j2
    apply Or.inl; apply types_are_values lem3 lem2
  case _ lem1 =>
    cases lem1; case _ lem1 =>
    cases lem1.2; cases lem1.1
case eq => apply Or.inl; apply Val.eq
case ite j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
  replace ih2 := ih2 h1
  cases ih2
  case _ v =>
    unfold ValidHeadVariable at j5
    unfold ValidHeadVariable at j6
    cases j5; case _ w1 j5 =>
    cases w1; case _ x1 sp1 =>
    cases j6; case _ w2 j6 =>
    cases w2; case _ x2 sp2 =>
    simp at *; cases v
    case app x3 sp3 h2 h3 =>
      generalize t1def : prefix_equal sp1 sp3 = t at *
      replace h3 := Eq.symm h3
      cases t
      case _ =>
        apply Or.inr; apply Exists.intro _
        apply Red.ite_missed j5.1 h3 h2 (Or.inr t1def)
      case _ q =>
        cases Nat.decEq x1 x3
        case _ h4 =>
          apply Or.inr; apply Exists.intro _
          apply Red.ite_missed j5.1 h3 h2 (Or.inl h4)
        case _ h4 =>
          subst h4; apply Or.inr; apply Exists.intro _
          apply Red.ite_matched j5.1 h3 (Eq.symm t1def) j5.2
    case choice v1 v2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.ite_map
    all_goals (cases j2; simp at j6)
  case _ ih2 =>
  cases ih2
  case _ ih2 =>
    cases ih2; case _ t ih2 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ite_congr ih2
  case _ ih2 =>
    subst ih2; apply Or.inr
    apply Exists.intro _
    apply Red.ite_absorb
case guard j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
  replace ih2 := ih2 h1
  cases ih2
  case _ v =>
    unfold ValidHeadVariable at j5
    unfold ValidHeadVariable at j6
    cases j5; case _ w1 j5 =>
    cases w1; case _ x1 sp1 =>
    cases j6; case _ w2 j6 =>
    cases w2; case _ x2 sp2 =>
    simp at *; cases v
    case app x3 sp3 h2 h3 =>
      generalize t1def : prefix_equal sp1 sp3 = t at *
      replace h3 := Eq.symm h3
      cases t
      case _ =>
        apply Or.inr; apply Exists.intro _
        apply Red.guard_missed j5.1 h3 h2 (Or.inr t1def)
      case _ q =>
        cases Nat.decEq x1 x3
        case _ h4 =>
          apply Or.inr; apply Exists.intro _
          apply Red.guard_missed j5.1 h3 h2 (Or.inl h4)
        case _ h4 =>
          subst h4; apply Or.inr; apply Exists.intro _
          apply Red.guard_matched j5.1 h3 (Eq.symm t1def)
    case choice v1 v2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.guard_map
    all_goals (cases j2; simp at j6)
  case _ ih2 =>
  cases ih2
  case _ ih2 =>
    cases ih2; case _ t ih2 =>
    apply Or.inr; apply Exists.intro _
    apply Red.guard_congr ih2
  case _ ih2 =>
    subst ih2; apply Or.inr
    apply Exists.intro _
    apply Red.guard_absorb
case lam => apply Or.inl; apply Val.lam
case app a _ j1 j2 j3 ih1 ih2 =>
  replace ih1 := ih1 h1
  cases ih1
  case _ v =>
    cases v
    case app x sp h1 h2 =>
      apply Or.inl; apply Val.app x (sp ++ [(.term, a)]) _ h1
      simp; rw [Option.bind_eq_some]; simp; rw [h2]
    case choice =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_map1 rfl; simp
    case lam =>
      apply Or.inr; apply Exists.intro _
      apply Red.beta
    all_goals (cases j1)
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb1 rfl
case lamt => apply Or.inl; apply Val.lamt
case appt  a _ j1 j2 j3 ih1 ih2 =>
  replace ih1 := ih1 h1
  cases ih1
  case _ v =>
    cases v
    case app x sp h1 h2 =>
      apply Or.inl; apply Val.app x (sp ++ [(.type, a)]) _ h1
      simp; rw [Option.bind_eq_some]; simp; rw [h2]
    case choice =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_map1 rfl; simp
    case lamt =>
      apply Or.inr; apply Exists.intro _
      apply Red.betat
    all_goals (cases j1)
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb1 rfl
case cast j1 j2 ih1 ih2 =>
  replace ih2 := ih2 h1
  cases ih2
  case _ v =>
    replace hv := refl_is_val j2 v
    cases hv
    case _ hv =>
      cases hv; case _ e1 e2 =>
      subst e1; subst e2
      apply Or.inr; apply Exists.intro _
      apply Red.cast
    case _ hv =>
      cases hv; case _ c1 hv =>
      cases hv; case _ c2 hv =>
      subst hv; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_map2 rfl; simp
  case _ ih2 =>
  cases ih2
  case _ ih2 =>
    cases ih2; case _ t ih2 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr2 rfl ih2
  case _ ih2 =>
    subst ih2; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb2 rfl
case refl => apply Or.inl; apply Val.refl
case sym j ih =>
  replace ih := ih h1
  cases ih
  case _ v =>
    have lem := refl_is_val j v
    cases lem
    case _ lem =>
      cases lem; case _ e1 e2 =>
      subst e1; subst e2
      apply Or.inr; apply Exists.intro _
      apply Red.sym
    case _ lem =>
      cases lem; case _ c1 lem =>
      cases lem; case _ c2 lem =>
      subst lem; apply Or.inr
      apply Exists.intro _
      apply Red.ctor1_map
  case _ ih =>
  cases ih
  case _ ih =>
    cases ih; case _ t ih =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor1_congr ih
  case _ ih =>
    subst ih; apply Or.inr
    apply Exists.intro _
    apply Red.ctor1_absorb
case seq j1 j2 ih1 ih2 =>
  replace ih1 := ih1 h1
  replace ih2 := ih2 h1
  cases ih1
  case _ v1 =>
    cases ih2
    case _ v2 =>
      replace v1 := refl_is_val j1 v1
      replace v2 := refl_is_val j2 v2
      cases v1
      case _ v1 =>
        cases v2
        case _ v2 =>
          cases v1; case _ e1 e2 =>
          cases v2; case _ e3 e4 =>
          subst e1; subst e2
          subst e3; subst e4
          apply Or.inr; apply Exists.intro _
          apply Red.seq
        case _ v2 =>
          cases v2; case _ c1 v2 =>
          cases v2; case _ c2 v2 =>
          subst v2; apply Or.inr
          apply Exists.intro _
          apply Red.ctor2_map2 rfl; simp
      case _ v1 =>
        cases v1; case _ c1 v1 =>
        cases v1; case _ c2 v1 =>
        subst v1; apply Or.inr
        apply Exists.intro _
        apply Red.ctor2_map1 rfl; simp
    case _ ih2 =>
    cases ih2
    case _ ih2 =>
      cases ih2; case _ t ih2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_congr2 rfl ih2
    case _ ih2 =>
      subst ih2; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_absorb2 rfl
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb1 rfl
case appc j1 j2 ih1 ih2 =>
  replace ih1 := ih1 h1
  replace ih2 := ih2 h1
  cases ih1
  case _ v1 =>
    cases ih2
    case _ v2 =>
      replace v1 := refl_is_val j1 v1
      replace v2 := refl_is_val j2 v2
      cases v1
      case _ v1 =>
        cases v2
        case _ v2 =>
          cases v1; case _ e1 e2 =>
          cases v2; case _ e3 e4 =>
          subst e1; subst e2
          subst e3; subst e4
          apply Or.inr; apply Exists.intro _
          apply Red.appc
        case _ v2 =>
          cases v2; case _ c1 v2 =>
          cases v2; case _ c2 v2 =>
          subst v2; apply Or.inr
          apply Exists.intro _
          apply Red.ctor2_map2 rfl; simp
      case _ v1 =>
        cases v1; case _ c1 v1 =>
        cases v1; case _ c2 v1 =>
        subst v1; apply Or.inr
        apply Exists.intro _
        apply Red.ctor2_map1 rfl; simp
    case _ ih2 =>
    cases ih2
    case _ ih2 =>
      cases ih2; case _ t ih2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_congr2 rfl ih2
    case _ ih2 =>
      subst ih2; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_absorb2 rfl
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb1 rfl
case arrowc j1 j2 ih1 ih2 =>
  replace ih1 := ih1 h1
  replace ih2 := ih2 (by
    intro x; unfold Frame.is_type
    cases x <;> simp at *
    unfold Frame.apply; simp
    case _ x =>
      replace h1 := h1 x
      rw [@Frame.is_type_apply _ _ _ S] at h1
      unfold Frame.is_type at h1
      apply h1)
  cases ih1
  case _ v1 =>
    cases ih2
    case _ v2 =>
      replace v1 := refl_is_val j1 v1
      replace v2 := refl_is_val j2 v2
      cases v1
      case _ v1 =>
        cases v2
        case _ v2 =>
          cases v1; case _ e1 e2 =>
          cases v2; case _ e3 e4 =>
          subst e1; subst e2
          subst e3; subst e4
          apply Or.inr; apply Exists.intro _
          apply Red.arrowc
        case _ v2 =>
          cases v2; case _ c1 v2 =>
          cases v2; case _ c2 v2 =>
          subst v2; apply Or.inr
          apply Exists.intro _
          apply Red.bind2_map2 rfl
      case _ v1 =>
        cases v1; case _ c1 v1 =>
        cases v1; case _ c2 v1 =>
        subst v1; apply Or.inr
        apply Exists.intro _
        apply Red.bind2_map1 rfl
    case _ ih2 =>
    cases ih2
    case _ ih2 =>
      cases ih2; case _ t ih2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.bind2_congr2 rfl
      simp; apply ih2
    case _ ih2 =>
      subst ih2; apply Or.inr
      apply Exists.intro _
      apply Red.bind2_absorb2 rfl
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.bind2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.bind2_absorb1 rfl
case fst j1 j2 j3 ih1 ih2 ih3 =>
  replace ih3 := ih3 h1
  cases ih3
  case _ v =>
    replace v := refl_is_val j3 v
    cases v
    case _ v =>
      cases v; case _ e1 e2 =>
      subst e1; injection e2 with _ e2 e3
      subst e2; subst e3
      apply Or.inr; apply Exists.intro _
      apply Red.fst
    case _ v =>
      cases v; case _ c1 v =>
      cases v; case _ c2 v =>
      subst v; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_map2 rfl; simp
  case _ ih3 =>
  cases ih3
  case _ ih3 =>
    cases ih3; case _ t ih3 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr2 rfl ih3
  case _ ih3 =>
    subst ih3; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb2 rfl
case snd j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  replace ih4 := ih4 h1
  cases ih4
  case _ v =>
    replace v := refl_is_val j4 v
    cases v
    case _ v =>
      cases v; case _ e1 e2 =>
      subst e1; injection e2 with _ e2 e3
      subst e2; subst e3
      apply Or.inr; apply Exists.intro _
      apply Red.snd
    case _ v =>
      cases v; case _ c1 v =>
      cases v; case _ c2 v =>
      subst v; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_map2 rfl; simp
  case _ ih4 =>
  cases ih4
  case _ ih4 =>
    cases ih4; case _ t ih4 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr2 rfl ih4
  case _ ih4 =>
    subst ih4; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb2 rfl
case allc j1 j2 ih1 ih2 =>
  replace ih2 := ih2 (by
    intro x; unfold Frame.is_type
    cases x <;> simp at *
    unfold Frame.apply; simp
    case _ x =>
      replace h1 := h1 x
      rw [@Frame.is_type_apply _ _ _ S] at h1
      unfold Frame.is_type at h1
      apply h1)
  cases ih2
  case _ v =>
    replace v := refl_is_val j2 v
    cases v
    case _ v =>
      cases v; case _ e1 e2 =>
      subst e1; subst e2
      apply Or.inr; apply Exists.intro _
      apply Red.allc
    case _ v =>
      cases v; case _ c1 v =>
      cases v; case _ c2 v =>
      subst v; apply Or.inr
      apply Exists.intro _
      apply Red.bind2_map2 rfl
  case _ ih2 =>
  cases ih2
  case _ ih2 =>
    cases ih2; case _ t ih2 =>
    apply Or.inr; apply Exists.intro _
    apply Red.bind2_congr2 rfl
    simp; apply ih2
  case _ ih2 =>
    subst ih2; apply Or.inr
    apply Exists.intro _
    apply Red.bind2_absorb2 rfl
case apptc Γ t1 K A B t2 C D _ _ j1 j2 j3 j4 ih1 ih2 =>
  replace ih1 := ih1 h1
  replace ih2 := ih2 h1
  cases ih1
  case _ v1 =>
    cases ih2
    case _ v2 =>
      replace v1 := refl_is_val j1 v1
      replace v2 := refl_is_val j2 v2
      cases v1
      case _ v1 =>
        cases v2
        case _ v2 =>
          cases v1; case _ e1 e2 =>
          cases v2; case _ e3 e4 =>
          subst e1; subst e3; subst e4
          injection e2 with _ _ e2; subst e2
          apply Or.inr; apply Exists.intro (refl! ★ (A β[C]))
          subst j3; apply Red.apptc
        case _ v2 =>
          cases v2; case _ c1 v2 =>
          cases v2; case _ c2 v2 =>
          subst v2; apply Or.inr
          apply Exists.intro _
          apply Red.ctor2_map2 rfl; simp
      case _ v1 =>
        cases v1; case _ c1 v1 =>
        cases v1; case _ c2 v1 =>
        subst v1; apply Or.inr
        apply Exists.intro _
        apply Red.ctor2_map1 rfl; simp
    case _ ih2 =>
    cases ih2
    case _ ih2 =>
      cases ih2; case _ t ih2 =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_congr2 rfl ih2
    case _ ih2 =>
      subst ih2; apply Or.inr
      apply Exists.intro _
      apply Red.ctor2_absorb2 rfl
  case _ ih1 =>
  cases ih1
  case _ ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih1
  case _ ih1 =>
    subst ih1; apply Or.inr
    apply Exists.intro _
    apply Red.ctor2_absorb1 rfl
case choice j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  replace ih3 := ih3 h1
  replace ih4 := ih4 h1
  cases ih3
  case _ v1 =>
    cases ih4
    case _ v2 =>
      apply Or.inl; apply Val.choice v1 v2
    case _ ih4 =>
    cases ih4
    case _ ih4 =>
      cases ih4; case _ t' ih4 =>
      apply Or.inr; apply Exists.intro _
      apply Red.ctor2_congr2 rfl ih4
    case _ ih4 =>
      subst ih4; apply Or.inr
      apply Exists.intro _
      apply Red.choice2
  case _ ih3 =>
  cases ih3
  case _ ih3 =>
    cases ih3; case _ t' ih3 =>
    apply Or.inr; apply Exists.intro _
    apply Red.ctor2_congr1 rfl ih3
  case _ ih3 =>
    subst ih3; apply Or.inr
    apply Exists.intro _
    apply Red.choice1

theorem progress :
  (∀ x, ¬ Γ.is_type x) ->
  Γ ⊢ t : A ->
  Val Γ t ∨ (∃ t', Red Γ t t') ∨ (t = `0)
:= by
intro h j
apply progress_lemma h j
