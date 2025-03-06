import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Uniqueness

theorem lift_subst_rename {Γ : Ctx Term} (A : Frame Term) :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n y, ^σ n = .re y -> ((A :: Γ) d@ n).apply (^σ) = (A.apply σ :: Δ) d@ y)
:= by
intro h1 n y h2
cases n
case _ =>
  simp at *; subst h2; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp
case _ n =>
  simp at *; unfold Subst.compose at h2; simp at h2
  generalize ydef : σ n = y at *
  cases y <;> simp at h2
  case _ z =>
    subst h2; simp
    replace h1 := h1 n z ydef
    rw [Frame.apply_compose]; simp; rw [<-h1]
    rw [Frame.apply_compose]

theorem lift_subst_stable {σ : Subst Term} (A : Frame Term) :
  (∀ n, (Γ d@ n).is_stable -> ∃ y, σ n = .re y) ->
  (∀ n, ((A :: Γ) d@ n).is_stable → ∃ y, (^σ) n = .re y)
:= by
intro h1 n h2
cases n <;> simp at *
case _ n =>
  rw [Frame.is_stable_stable] at h2
  unfold Subst.compose; simp
  replace h1 := h1 n h2
  cases h1; case _ z h2 =>
    rw [h2]; simp

theorem neutral_form_subst {t : Term} (σ : Subst Term) :
  (σ x = .re y) ->
  t.neutral_form = .some (x, sp) ->
  ([σ]t).neutral_form = .some (y, List.map (λ (v, l) => (v, [σ]l)) sp)
:= by
intro h1 h2
induction t generalizing σ y x sp
case ctor2 v t1 t2 ih1 ih2 =>
  cases v; any_goals try simp at h2
  all_goals
    case _ =>
    rw [Option.bind_eq_some] at h2
    cases h2; case _ a h2 =>
    cases h2; case _ h2 h3 =>
      injection h3 with e; simp at *;
      cases e; case _ e1 e2 =>
        rw [Option.bind_eq_some]; subst e1; subst e2; simp
        cases a; case _ ax asp =>
          replace ih1 := ih1 σ h1 h2; simp at ih1
          unfold Subst.apply at ih1; simp at ih1
          exists y; exists (List.map (fun x => (x.fst, [σ]x.snd)) asp)
all_goals simp at h2
case _ z =>
  cases h2; case _ e1 e2 =>
    subst e1; subst e2; simp
    rw [h1]; simp

theorem valid_head_variable_subst test σtest :
  (∀ n, test n -> ∃ y, σ n = .re y ∧ σtest y) ->
  ValidHeadVariable A test ->
  ValidHeadVariable ([σ]A) σtest
:= by
intro q h; unfold ValidHeadVariable at *; simp at *
cases h; case _ x h =>
cases h; case _ h1 h2 =>
cases h1; case _ sp h1 =>
  have lem1 := q x h2
  cases lem1; case _ y lem1 =>
  cases lem1; case _ lem1 lem2 =>
    replace h1 := neutral_form_subst σ lem1 (Eq.symm h1); simp at h1
    exists y; rw [lem2]; simp
    rw [h1]; simp

theorem valid_ctor_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  ValidCtor Γ A ->
  ValidCtor Δ ([σ]A)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ R Γ j =>
  constructor; apply valid_head_variable_subst Γ.is_datatype Δ.is_datatype _ j
  intro n h3
  have lem1 := Frame.is_datatype_implies_is_stable h3
  replace h2 := h2 n lem1
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_datatype_stable]
    simp at h3; apply h3
case _ Γ A B j ih =>
  simp; apply ValidCtor.arrow
  replace ih := @ih (^σ)
    (((Frame.type A).apply σ) :: Δ)
    (lift_subst_rename (Frame.type A) h1)
    (lift_subst_stable (Frame.type A) h2)
  simp at ih; apply ih
case _ Γ A B j ih =>
  simp; apply ValidCtor.all
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (lift_subst_rename (Frame.kind A) h1)
    (lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem valid_insttype_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  ValidInstType Γ A ->
  ValidInstType Δ ([σ]A)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ R Γ j =>
  constructor; apply valid_head_variable_subst Γ.is_opent Δ.is_opent _ j
  intro n h3
  have lem1 := Frame.is_opent_implies_is_stable h3
  replace h2 := h2 n lem1
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_opent_stable]
    simp at h3; apply h3
case _ Γ A B j ih =>
  simp; apply ValidInstType.arrow
  replace ih := @ih (^σ)
    (((Frame.type A).apply σ) :: Δ)
    (lift_subst_rename (Frame.type A) h1)
    (lift_subst_stable (Frame.type A) h2)
  simp at ih; apply ih
case _ Γ A B j ih =>
  simp; apply ValidInstType.all
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (lift_subst_rename (Frame.kind A) h1)
    (lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem stable_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  StableTypeMatch Γ A B ->
  StableTypeMatch Δ ([σ]A) ([σ]B)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ R Γ j =>
  constructor; apply valid_head_variable_subst Γ.is_stable Δ.is_stable _ j
  intro n h3; replace h2 := h2 n h3
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_stable_stable]
    simp at h3; apply h3
case _ R Γ A B j1 j2 ih =>
  replace ih := @ih (^σ)
    (((Frame.type A).apply σ) :: Δ)
    (lift_subst_rename (Frame.type A) h1)
    (lift_subst_stable (Frame.type A) h2)
  simp at ih;
  simp; constructor; simp
  case _ =>
    apply valid_head_variable_subst Γ.is_stable Δ.is_stable _ j1
    intro n h3; replace h2 := h2 n h3
    cases h2; case _ w h2 =>
      exists w; rw [h2]; simp
      rw [<-h1 n w h2, Frame.is_stable_stable]
      simp at h3; apply h3
  case _ => simp; apply ih
case _ R Γ A B j1 j2 ih =>
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (lift_subst_rename (Frame.kind A) h1)
    (lift_subst_stable (Frame.kind A) h2)
  simp at ih;
  simp; constructor; simp
  case _ =>
    apply valid_head_variable_subst Γ.is_stable Δ.is_stable _ j1
    intro n h3; replace h2 := h2 n h3
    cases h2; case _ w h2 =>
      exists w; rw [h2]; simp
      rw [<-h1 n w h2, Frame.is_stable_stable]
      simp at h3; apply h3
  case _ => simp; apply ih

theorem stable_type_match_beta t :
  ¬ f.is_stable ->
  StableTypeMatch (f :: Γ) A B ->
  StableTypeMatch Γ (A β[t]) (B β[t])
:= by
intro j1 j2
apply stable_type_match_subst _ _ j2
case _ =>
  intro n y h
  cases n <;> simp at *
  case _ x =>
    subst h; rw [Frame.apply_compose]; simp
case _ =>
  intro n h1; cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  rw [h1] at j1; injection j1

theorem prefix_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  PrefixTypeMatch Γ A B T ->
  PrefixTypeMatch Δ ([σ]A) ([σ]B) ([σ]T)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ Γ B j =>
  constructor; apply valid_head_variable_subst Γ.is_stable Δ.is_stable _ j
  intro n h3; replace h2 := h2 n h3
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_stable_stable]
    simp at h3; apply h3
case _ Γ A B V T j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.type A).apply σ) :: Δ)
    (lift_subst_rename (Frame.type A) h1)
    (lift_subst_stable (Frame.type A) h2)
  simp at ih; apply ih
case _ Γ A B V T j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (lift_subst_rename (Frame.kind A) h1)
    (lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem prefix_type_match_beta t :
  ¬ f.is_stable ->
  PrefixTypeMatch (f :: Γ) A B T ->
  PrefixTypeMatch Γ (A β[t]) (B β[t]) (T β[t])
:= by
intro j1 j2
apply prefix_type_match_subst _ _ j2
case _ =>
  intro n y h
  cases n <;> simp at *
  case _ x =>
    subst h; rw [Frame.apply_compose]; simp
case _ =>
  intro n h1; cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  rw [h1] at j1; injection j1

theorem no_infinite_terms_arrow σ :
  ¬ ([σ](A -t> B) = B)
:= by
intro h
induction B generalizing σ A <;> simp at *
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  cases h; case _ h1 h2 =>
    subst h1; replace ih2 := @ih2 ([σ]A) (^σ)
    simp at ih2; apply ih2; simp at h2; rw [h2]

theorem stable_type_match_refl_inversion :
  StableTypeMatch Γ A A ->
  ValidHeadVariable A Γ.is_stable
:= by
intro j; cases j <;> simp [*]

theorem prefix_type_match_forced_refl :
  ValidHeadVariable A Γ.is_stable ->
  PrefixTypeMatch Γ A B T ->
  B = T
:= by
intro j1 j2
cases j2
case _ => rfl
case _ =>
  exfalso
  apply no_valid_head_variable_with_arrow j1
case _ =>
  exfalso
  apply no_valid_head_variable_with_all j1


theorem datatype_indexing_exists {Γ : Ctx Term} : (Γ d@ n).is_datatype = true -> ∃ t, Γ d@ n = .datatype t := by
intros h;
unfold Frame.is_datatype at h; simp at h;
split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

theorem insttype_indexing_exists {Γ : Ctx Term} : (Γ d@ n).is_insttype = true -> ∃ t, Γ d@ n = .insttype t := by
intros h;
unfold Frame.is_insttype at h; simp at h;
split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

theorem opent_indexing_exists {Γ : Ctx Term} : (Γ d@ n).is_opent = true -> ∃ t, Γ d@ n = .opent t := by
intros h;
unfold Frame.is_opent at h; simp at h;
split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

theorem indexing_uniqueness_datatype {Γ : Ctx Term} : (Γ d@ t).is_datatype -> (Γ d@ t).is_opent -> False := by
intro h1 h2;
replace h1 := datatype_indexing_exists h1;
cases h1; case _ h1 =>
rw [h1]at h2; unfold Frame.is_opent at h2; simp at h2

theorem indexing_uniqueness_opent {Γ : Ctx Term} : (Γ d@ t).is_opent -> (Γ d@ t).is_datatype -> False := by
intro h1 h2;
replace h1 := opent_indexing_exists h1;
cases h1; case _ h1 =>
rw [h1]at h2; unfold Frame.is_datatype at h2; simp at h2

theorem datatype_opent_distinct : ValidCtor Γ T -> ValidInstType Γ T -> False := by
intros vctor vit;
cases vctor;
case refl h1 =>
  cases vit;
  case refl h2 =>
    unfold ValidHeadVariable at h1; unfold ValidHeadVariable at h2
    cases h1; case _ h1 =>
    cases h1; case _ tnf dt =>
    cases h2; case _ h2 =>
    cases h2; case _ tnf' ot =>
    rw[<-tnf] at tnf'; cases tnf'; simp at *;
    apply indexing_uniqueness_datatype dt ot;
  case arrow h2 =>
    cases h1;
    case _ ts h1 =>
      cases h1; case _ nf _ => cases nf;
  case all h2 =>
    cases h1;
    case _ ts h1 =>
      cases h1; case _ nf _ => cases nf;
case arrow h1 =>
  cases vit;
  case refl h2 =>
    cases h2;
    case _ h2 =>
    cases h2; case _ nf _ => cases nf
  case arrow h2 =>
    apply datatype_opent_distinct h1 h2
case all h1 =>
  cases vit;
  case refl h2 =>
    cases h2; case _ h2 =>
    cases h2; case _ nf _ => cases nf
  case all h2 =>
    apply datatype_opent_distinct h1 h2
