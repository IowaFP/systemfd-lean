import SystemFD.Util
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

theorem neutral_form_rename {t : Term} (r : Ren) :
  t.neutral_form = q ->
  ([r.to]t).neutral_form = Option.map (λ (x, l) => (r x, List.map (λ (v, t) => (v, [r.to]t)) l)) q
:= by
intro h
induction t generalizing r q
any_goals try (simp at h; subst h; simp)
case _ v t1 t2 ih1 ih2 =>
  cases v; any_goals try solve | (simp at h; subst h; simp)
  all_goals case _ =>
    cases q
    case _ =>
      simp at h; simp; intro a b h2
      have lem : t1.neutral_form = .none := by
        apply option_lemma; intro v
        apply h v.fst v.snd
      replace ih1 := @ih1 .none r lem; simp at ih1
      unfold Subst.apply at ih1; simp at ih1; rw [h2] at ih1
      injection ih1
    case _ v =>
      simp at h; simp; rw [Option.bind_eq_some] at h
      cases h; case _ a h =>
      cases h; case _ h1 h2 =>
        injection h2 with e; rw [Option.bind_eq_some]; subst e; simp
        replace ih1 := ih1 r h1; simp at ih1
        exists (r a.fst); exists (List.map (fun x => (x.fst, [r.to]x.snd)) a.snd)

theorem stable_type_match_sound_lemma :
  (τ, sR) = Term.to_telescope A ->
  [S' τ.length]R = sR ->
  .some (x, sp) = Term.neutral_form R ->
  (Γ d@ x).is_stable ->
  StableTypeMatch Γ A R
:= by
intro h1 h2 h3 h4
induction A generalizing τ sR R x sp Γ <;> try simp at h1
any_goals try (
  case _ =>
    cases h1; case _ e1 e2 =>
      subst e1; subst e2
      simp at h2; subst h2; constructor
      unfold ValidHeadVariable;
      apply Exists.intro _; apply And.intro
      apply h3; apply h4
)
case _ v t1 t2 ih1 ih2 =>
  cases v <;> try simp at h1
  any_goals try (
    case _ =>
      cases h1; case _ e1 e2 =>
        subst e1; subst e2
        simp at h2; subst h2; constructor
        unfold ValidHeadVariable;
        apply Exists.intro _; apply And.intro
        apply h3; apply h4
  )
  case all =>
    cases τ
    case _ => simp at h1
    case _ hd τ =>
      have lem1 : (τ, sR) = t2.to_telescope := by
        cases h1; case _ u1 u2 =>
          subst u2; injection u1 with _ e; subst e
          generalize zdef : t2.to_telescope = z
          apply Prod.eta
      have lem2 : [S' τ.length][S]R = sR := by simp at h2; simp [*]
      have lem3 :
        .some (x + 1, List.map (λ (v, t) => (v, [S]t)) sp)
        = ([S]R).neutral_form
      := by
        replace h3 := Eq.symm h3
        have lem := neutral_form_rename (fun x => x + 1) h3
        rw [Subst.to_S] at lem; rw [lem]; simp
      have lem4 : ((Frame.kind t1 :: Γ)d@(x + 1)).is_stable := by
        simp; rw [Frame.is_stable_stable]; apply h4
      apply StableTypeMatch.all
      case _ =>
        simp at *; unfold ValidHeadVariable
        have lem5 : @Ren.to Term (· - 1) = P := by
          unfold Ren.to; unfold P; simp
        have lem6 := neutral_form_rename (· - 1) (Eq.symm lem3)
        rw [lem5] at lem6; simp at lem6
        rw [Frame.is_stable_stable] at lem4
        unfold Function.comp at lem6; simp at lem6
        apply Exists.intro (x, sp)
        apply And.intro (Eq.symm lem6); simp
        apply lem4
      case _ => apply ih2 lem1 lem2 lem3 lem4
  case arrow =>
    cases τ
    case _ => simp at h1
    case _ hd τ =>
      have lem1 : (τ, sR) = t2.to_telescope := by
        cases h1; case _ u1 u2 =>
          subst u2; injection u1 with _ e; subst e
          generalize zdef : t2.to_telescope = z
          apply Prod.eta
      have lem2 : [S' τ.length][S]R = sR := by simp at h2; simp [*]
      have lem3 :
        .some (x + 1, List.map (λ (v, t) => (v, [S]t)) sp)
        = ([S]R).neutral_form
      := by
        replace h3 := Eq.symm h3
        have lem := neutral_form_rename (fun x => x + 1) h3
        rw [Subst.to_S] at lem; rw [lem]; simp
      have lem4 : ((Frame.type t1 :: Γ)d@(x + 1)).is_stable := by
        simp; rw [Frame.is_stable_stable]; apply h4
      apply StableTypeMatch.arrow
      case _ =>
        simp at *; unfold ValidHeadVariable
        have lem5 : @Ren.to Term (· - 1) = P := by
          unfold Ren.to; unfold P; simp
        have lem6 := neutral_form_rename (· - 1) (Eq.symm lem3)
        rw [lem5] at lem6; simp at lem6
        rw [Frame.is_stable_stable] at lem4
        unfold Function.comp at lem6; simp at lem6
        apply Exists.intro (x, sp)
        apply And.intro (Eq.symm lem6); simp
        apply lem4
      case _ => apply ih2 lem1 lem2 lem3 lem4

theorem stable_type_match_sound :
  stable_type_match Γ A R = .some u ->
  StableTypeMatch Γ A R
:= by
intro h
unfold stable_type_match at h
simp at h; rw [Option.bind_eq_some] at h; simp at h
cases h; case _ a h =>
cases h; case _ h1 h2 =>
cases h1; case _ sp h1 =>
cases h2; case _ h2 h3 =>
  generalize sRdef : A.to_telescope = Asp at *
  cases Asp; case _ τ sR =>
    replace h2 := Term.eq_of_beq h2; simp at *
    apply stable_type_match_sound_lemma
      (Eq.symm sRdef) h2 (Eq.symm h1) h3

theorem telescope_empty {B : Term} :
  ([], sB) = B.to_telescope ->
  sB = B
:= by
intro h; induction B generalizing sB <;> simp at * <;> try simp [*]
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at * <;> try simp [*]

theorem telescope_valid_frames {B : Term} :
  (f :: τ, sB) = B.to_telescope ->
  (∃ t, f = .type t) ∨ (∃ t, f = .kind t)
:= by
intro h; induction B generalizing f τ sB <;> simp at *
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  case _ => apply Or.inr; exists t1; apply h.1.1
  case _ => apply Or.inl; exists t1; apply h.1.1

theorem telescope_type_head {B : Term} :
  (.type A :: τ, sB) = B.to_telescope ->
  ∃ D, B = (A -t> D) ∧ (τ, sB) = D.to_telescope
:= by
intro h; induction B generalizing A τ sB <;> simp at *
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  case _ =>
    cases h; case _ h1 h2 =>
    cases h1; case _ h1 h3 =>
      subst h1; subst h2; subst h3
      exists t2

theorem telescope_kind_head {B : Term} :
  (.kind A :: τ, sB) = B.to_telescope ->
  ∃ D, B = (∀[A] D) ∧ (τ, sB) = D.to_telescope
:= by
intro h; induction B generalizing A τ sB <;> simp at *
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  case _ =>
    cases h; case _ h1 h2 =>
    cases h1; case _ h1 h3 =>
      subst h1; subst h2; subst h3
      exists t2

theorem telescope_rev_append_type :
  Term.from_telescope_rev (Γ ++ [Frame.type A]) t = (A -t> (Term.from_telescope_rev Γ t))
:= by
induction Γ generalizing A t <;> simp at *
case _ hd tl ih =>
  cases hd <;> simp at *
  any_goals case _ => rw [ih]


theorem telescope_rev_append_kind :
  Term.from_telescope_rev (Γ ++ [Frame.kind A]) t = (∀[A] (Term.from_telescope_rev Γ t))
:= by
induction Γ generalizing A t <;> simp at *
case _ hd tl ih =>
  cases hd <;> simp at *
  any_goals case _ => rw [ih]

theorem to_from_telescope {B : Term} :
  (τ, sB) = B.to_telescope ->
  sB.from_telescope τ = B
:= by
intro h; induction B generalizing τ sB <;> simp at *
case bind2 v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  case all =>
    cases h; case _ h1 h2 =>
      subst h1; subst h2; simp
      rw [telescope_rev_append_kind, ih2 rfl]
  case arrow =>
    cases h; case _ h1 h2 =>
      subst h1; subst h2; simp
      rw [telescope_rev_append_type, ih2 rfl]
  all_goals (
    cases h; case _ h1 h2 =>
      subst h1; subst h2; simp)
all_goals (
  cases h; case _ h1 h2 =>
    subst h1; subst h2; simp)

theorem prefix_type_match_sound_lemma :
  (τ, sR) = Term.to_telescope A ->
  (τ', sT) = Term.to_telescope B ->
  .some ξ = prefix_equal τ τ' ->
  [S' τ.length]T = Term.from_telescope ξ sT ->
  [S' τ.length]R = sR ->
  .some (x, sp) = Term.neutral_form R ->
  (Γ d@ x).is_stable ->
  PrefixTypeMatch Γ A B T
:= by
intro h1 h2 h3 h4 h5 h6 h7
induction τ, τ' using prefix_equal.induct generalizing Γ x sp sR R A sT B ξ T
case _ t =>
  simp at *; subst h3; subst h4
  replace h1 := telescope_empty h1; subst h1; subst h5
  have lem : sT.from_telescope ξ = B := by apply to_from_telescope h2
  simp at lem; rw [lem]
  have vhv : ValidHeadVariable R Γ.is_stable := by
       unfold ValidHeadVariable; apply Exists.intro (x, sp) (And.intro h6 h7);
  apply PrefixTypeMatch.refl vhv
case _ => simp at *
case _ x1 t1 x2 t2 _ ih1 =>
  simp at h3; cases h3; case _ h3e h3 =>
    replace h3e := Frame.eq_of_beq h3e; subst h3e
    have lem1 := telescope_valid_frames h2
    cases lem1
    case _ lem1 =>
      cases lem1; case _ u lem1 =>
        subst lem1
        replace h1 := telescope_type_head h1
        replace h2 := telescope_type_head h2
        cases h1; case _ D1 h1 =>
        cases h1; case _ h1 h1' =>
        cases h2; case _ D2 h2 =>
        cases h2; case _ h2 h2' =>
          subst h1; subst h2; simp at h4; simp at h5
          replace h6 := neutral_form_rename (fun x => x + 1) (Eq.symm h6); rw [Subst.to_S] at h6
          simp at h6; constructor
          replace ih1 := @ih1 sR D1 sT D2 ξ ([S]T) ([S]R) (x + 1)
            (List.map (λ (v, t) => (v, [S]t)) sp) (.type u::Γ) h1' h2' h3
          simp at ih1; replace ih1 := ih1 h4 h5 (Eq.symm h6)
          apply ih1; rw [Frame.is_stable_stable]; apply h7
    case _ lem1 =>
      cases lem1; case _ u lem1 =>
        subst lem1
        replace h1 := telescope_kind_head h1
        replace h2 := telescope_kind_head h2
        cases h1; case _ D1 h1 =>
        cases h1; case _ h1 h1' =>
        cases h2; case _ D2 h2 =>
        cases h2; case _ h2 h2' =>
          subst h1; subst h2; simp at h4; simp at h5
          replace h6 := neutral_form_rename (fun x => x + 1) (Eq.symm h6); rw [Subst.to_S] at h6
          simp at h6; constructor
          replace ih1 := @ih1 sR D1 sT D2 ξ ([S]T) ([S]R) (x + 1)
            (List.map (λ (v, t) => (v, [S]t)) sp) (.kind u::Γ) h1' h2' h3
          simp at ih1; replace ih1 := ih1 h4 h5 (Eq.symm h6)
          apply ih1; rw [Frame.is_stable_stable]; apply h7
case _ h =>
  simp at h3; replace h := not_eq_of_beq h
  cases h3; case _ h3e h3 =>
    replace h3e := Frame.eq_of_beq h3e; subst h3e
    exfalso; apply h rfl

theorem prefix_type_match_sound :
  prefix_type_match Γ A B = .some T ->
  PrefixTypeMatch Γ A B T
:= by
intros h;
unfold prefix_type_match at h; simp at h
rw [Option.bind_eq_some] at h
cases h; case _ ξ h =>
cases h; case _ h1 h2 =>
rw [Option.bind_eq_some] at h2; simp at h2
cases h2; case _ x h2 =>
cases h2; case _ h2 h3 =>
cases h3; case _ h3 h4 =>
cases h3; case _ h3 h5 =>
cases h3; case _ h3 h6 =>
cases h2; case _ sp h2 =>
  generalize Aspdef : A.to_telescope = Asp at *
  generalize Bspdef : B.to_telescope = Bsp at *
  cases Asp; case _ τ sR =>
  cases Bsp; case _ τ' sT =>
    simp at *
    replace h6 := Term.eq_of_beq h6
    replace h3 := Term.eq_of_beq h3
    apply prefix_type_match_sound_lemma
      (Eq.symm Aspdef) (Eq.symm Bspdef) (Eq.symm h1)
    rw [<-h4]; simp; apply h3
    rw [<-Subst.apply_compose_commute] at h6
    apply h6; apply Eq.symm h2
    apply h5

theorem valid_ctor_sound_lemma :
  (τ, R) = Term.to_telescope A ->
  .some (x, sp) = Term.neutral_form R ->
  x' = x - τ.length ->
  x = x' + τ.length ->
  (Γ d@ x').is_datatype ->
  ValidCtor Γ A
:= by
intro h1 h2 h3 h4 h5
induction A generalizing τ R x sp x' Γ <;> try simp at h1
any_goals try (
  case _ =>
    cases h1; case _ e1 e2 =>
      subst e1; subst e2
      constructor; unfold ValidHeadVariable
      apply Exists.intro _; apply And.intro
      apply h2; subst h3; simp; apply h5
)
case _ v t1 t2 ih1 ih2 =>
  cases v <;> try simp at h1
  any_goals try (
    cases h1; case _ e1 e2 =>
      subst e1; subst e2
      constructor; unfold ValidHeadVariable
      apply Exists.intro _; apply And.intro
      apply h2; subst h3; simp; apply h5
  )
  case _ =>
    generalize Bdef : t2.to_telescope = B at *
    cases B; case _ γ rB =>
    cases h1; case _ h1 h2 =>
      subst h1; subst h2; simp at *
      have lem1 : x' + 1 = x - γ.length := by omega
      have lem2 : x = x' + 1 + γ.length := by omega
      apply ValidCtor.all
      apply ih2 rfl rfl h2 lem1 lem2
      simp; rw [Frame.is_datatype_stable]; apply h5
  case _ =>
    generalize Bdef : t2.to_telescope = B at *
    cases B; case _ γ rB =>
    cases h1; case _ h1 h2 =>
      subst h1; subst h2; simp at *
      have lem1 : x' + 1 = x - γ.length := by omega
      have lem2 : x = x' + 1 + γ.length := by omega
      apply ValidCtor.arrow
      apply ih2 rfl rfl h2 lem1 lem2
      simp; rw [Frame.is_datatype_stable]; apply h5

theorem valid_ctor_sound : valid_ctor Γ A = .some () -> ValidCtor Γ A := by
intro h
unfold valid_ctor at h; simp at h
rw [Option.bind_eq_some] at h; simp at h
cases h; case _ a h =>
cases h; case _ h1 h2 =>
cases h2; case _ h2 h3 =>
  generalize Aspdef : A.to_telescope = Asp at *
  cases Asp; case _ τ sA =>
  cases h1; case _ sp h1 =>
    simp at *
    apply valid_ctor_sound_lemma
      (Eq.symm Aspdef) (Eq.symm h1) rfl h2 h3

theorem valid_insttype_sound_lemma :
  (τ, R) = Term.to_telescope A ->
  .some (x, sp) = Term.neutral_form R ->
  x' = x - τ.length ->
  x = x' + τ.length ->
  (Γ d@ x').is_opent ->
  ValidInstType Γ A
:= by
intro h1 h2 h3 h4 h5
induction A generalizing τ R x sp x' Γ <;> try simp at h1
any_goals try (
  case _ =>
    cases h1; case _ e1 e2 =>
      subst e1; subst e2
      constructor; unfold ValidHeadVariable
      apply Exists.intro _; apply And.intro
      apply h2; subst h3; simp; apply h5
)
case _ v t1 t2 ih1 ih2 =>
  cases v <;> try simp at h1
  any_goals try (
    cases h1; case _ e1 e2 =>
      subst e1; subst e2
      constructor; unfold ValidHeadVariable
      apply Exists.intro _; apply And.intro
      apply h2; subst h3; simp; apply h5
  )
  case _ =>
    generalize Bdef : t2.to_telescope = B at *
    cases B; case _ γ rB =>
    cases h1; case _ h1 h2 =>
      subst h1; subst h2; simp at *
      have lem1 : x' + 1 = x - γ.length := by omega
      have lem2 : x = x' + 1 + γ.length := by omega
      apply ValidInstType.all
      apply ih2 rfl rfl h2 lem1 lem2
      simp; rw [Frame.is_opent_stable]; apply h5
  case _ =>
    generalize Bdef : t2.to_telescope = B at *
    cases B; case _ γ rB =>
    cases h1; case _ h1 h2 =>
      subst h1; subst h2; simp at *
      have lem1 : x' + 1 = x - γ.length := by omega
      have lem2 : x = x' + 1 + γ.length := by omega
      apply ValidInstType.arrow
      apply ih2 rfl rfl h2 lem1 lem2
      simp; rw [Frame.is_opent_stable]; apply h5

theorem valid_insttype_sound : valid_insttype Γ A = .some () -> ValidInstType Γ A := by
intro h
unfold valid_insttype at h; simp at h
rw [Option.bind_eq_some] at h; simp at h
cases h; case _ a h =>
cases h; case _ h1 h2 =>
cases h2; case _ h2 h3 =>
  generalize Aspdef : A.to_telescope = Asp at *
  cases Asp; case _ τ sA =>
  cases h1; case _ sp h1 =>
    simp at *
    apply valid_insttype_sound_lemma
      (Eq.symm Aspdef) (Eq.symm h1) rfl h2 h3
