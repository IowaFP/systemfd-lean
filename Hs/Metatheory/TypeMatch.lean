import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx


theorem hs_lift_subst_rename {Γ : Ctx HsTerm} (A : Frame HsTerm) :
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

theorem hs_lift_subst_stable {σ : Subst HsTerm} (A : Frame HsTerm) :
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

theorem hs_neutral_form_subst {t : HsTerm} (σ : Subst HsTerm) :
  (σ x = .re y) ->
  t.neutral_form = .some (x, sp) ->
  ([σ]t).neutral_form = .some (y, List.map (λ (v, l) => (v, [σ]l)) sp)
:= by
intro h1 h2
induction t generalizing σ y x sp
case HsCtor2 v t1 t2 ih1 ih2 =>
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
          apply ih1
all_goals simp at h2
case _ z =>
  cases h2; case _ e1 e2 =>
    subst e1; subst e2; simp
    rw [h1]; simp

theorem hs_valid_head_variable_subst test σtest :
  (∀ n, test n -> ∃ y, σ n = .re y ∧ σtest y) ->
  HsValidHeadVariable A test ->
  HsValidHeadVariable ([σ]A) σtest
:= by
intro q h; unfold HsValidHeadVariable at *; simp at *
cases h; case _ x h =>
cases h; case _ h1 h2 =>
cases h1; case _ sp h1 =>
  have lem1 := q x h2
  cases lem1; case _ y lem1 =>
  cases lem1; case _ lem1 lem2 =>
    replace h1 := hs_neutral_form_subst σ lem1 (Eq.symm h1); simp at h1
    exists y; rw [lem2]; simp
    rw [h1]; simp

theorem hs_valid_ctor_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  ValidHsCtorType Γ A ->
  ValidHsCtorType Δ ([σ]A)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case refl R Γ j =>
  constructor; apply hs_valid_head_variable_subst Γ.is_datatype Δ.is_datatype _ j
  intro n h3
  have lem1 := Frame.is_datatype_implies_is_stable h3
  replace h2 := h2 n lem1
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_datatype_stable]
    simp at h3; apply h3
case _ Γ A B j ih =>
  simp; apply ValidHsCtorType.arrow
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih; apply ih
case _ Γ A B j ih =>
  simp; apply ValidHsCtorType.farrow
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih; apply ih
case _ Γ A B j ih =>
  simp; apply ValidHsCtorType.all
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.kind A) h1)
    (hs_lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem hs_valid_insttype_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  ValidHsInstType Γ A ->
  ValidHsInstType Δ ([σ]A)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ R Γ j =>
  constructor; apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent _ j
  intro n h3
  have lem1 := Frame.is_opent_implies_is_stable h3
  replace h2 := h2 n lem1
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_opent_stable]
    simp at h3; apply h3
case _ Γ A B j ih =>
  simp; apply ValidHsInstType.arrow
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih; apply ih
case _ Γ A B j ih =>
  simp; apply ValidHsInstType.farrow
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih; apply ih

case _ Γ A B j ih =>
  simp; apply ValidHsInstType.all
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.kind A) h1)
    (hs_lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem hs_stable_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  StableHsTypeMatch Γ A B ->
  StableHsTypeMatch Δ ([σ]A) ([σ]B)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ R Γ j =>
  constructor; apply hs_valid_head_variable_subst Γ.is_stable Δ.is_stable _ j
  intro n h3; replace h2 := h2 n h3
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_stable_stable]
    simp at h3; apply h3
case _ R Γ A B j1 j2 ih =>
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih;
  simp; constructor; simp
  case _ =>
    apply hs_valid_head_variable_subst Γ.is_stable Δ.is_stable _ j1
    intro n h3; replace h2 := h2 n h3
    cases h2; case _ w h2 =>
      exists w; rw [h2]; simp
      rw [<-h1 n w h2, Frame.is_stable_stable]
      simp at h3; apply h3
  case _ => simp; apply ih
case _ R Γ A B j1 j2 ih =>
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih;
  simp; constructor; simp
  case _ =>
    apply hs_valid_head_variable_subst Γ.is_stable Δ.is_stable _ j1
    intro n h3; replace h2 := h2 n h3
    cases h2; case _ w h2 =>
      exists w; rw [h2]; simp
      rw [<-h1 n w h2, Frame.is_stable_stable]
      simp at h3; apply h3
  case _ => simp; apply ih
case _ R Γ A B j1 j2 ih =>
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.kind A) h1)
    (hs_lift_subst_stable (Frame.kind A) h2)
  simp at ih;
  simp; constructor; simp
  case _ =>
    apply hs_valid_head_variable_subst Γ.is_stable Δ.is_stable _ j1
    intro n h3; replace h2 := h2 n h3
    cases h2; case _ w h2 =>
      exists w; rw [h2]; simp
      rw [<-h1 n w h2, Frame.is_stable_stable]
      simp at h3; apply h3
  case _ => simp; apply ih

theorem hs_stable_type_match_beta t :
  ¬ f.is_stable ->
  StableHsTypeMatch (f :: Γ) A B ->
  StableHsTypeMatch Γ (A β[t]) (B β[t])
:= by
intro j1 j2
apply hs_stable_type_match_subst _ _ j2
case _ =>
  intro n y h
  cases n <;> simp at *
  case _ x =>
    subst h; rw [Frame.apply_compose]; simp
case _ =>
  intro n h1; cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  rw [h1] at j1; injection j1

theorem hs_prefix_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  PrefixHsTypeMatch Γ A B T ->
  PrefixHsTypeMatch Δ ([σ]A) ([σ]B) ([σ]T)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ Γ B j =>
  constructor; apply hs_valid_head_variable_subst Γ.is_stable Δ.is_stable _ j
  intro n h3; replace h2 := h2 n h3
  cases h2; case _ w h2 =>
    exists w; rw [h2]; simp
    rw [<-h1 n w h2, Frame.is_stable_stable]
    simp at h3; apply h3
case _ Γ A B V T j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.empty).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.empty) h1)
    (hs_lift_subst_stable (Frame.empty) h2)
  simp at ih; apply ih
case _ Γ A B V T j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (hs_lift_subst_rename (Frame.kind A) h1)
    (hs_lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem hs_prefix_type_match_beta t :
  ¬ f.is_stable ->
  PrefixHsTypeMatch (f :: Γ) A B T ->
  PrefixHsTypeMatch Γ (A β[t]) (B β[t]) (T β[t])
:= by
intro j1 j2
apply hs_prefix_type_match_subst _ _ j2
case _ =>
  intro n y h
  cases n <;> simp at *
  case _ x =>
    subst h; rw [Frame.apply_compose]; simp
case _ =>
  intro n h1; cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  rw [h1] at j1; injection j1

theorem hs_no_infinite_terms_arrow σ :
  ¬ ([σ](A -t> B) = B)
:= by
intro h
induction B generalizing σ A <;> simp at *
case _ v t1 t2 ih1 ih2 =>
  cases v <;> simp at *
  cases h; case _ h1 h2 =>
    subst h1; replace ih2 := @ih2 ([σ]A) (^σ)
    simp at ih2; apply ih2; simp at h2; rw [h2]

theorem hs_stable_type_match_refl_inversion :
  StableHsTypeMatch Γ A A ->
  HsValidHeadVariable A Γ.is_stable
:= by
intro j; cases j <;> simp [*]

theorem hs_no_valid_head_variable_with_all :
  ¬ HsValidHeadVariable (`∀{A}B) test
:= by
intro h; unfold HsValidHeadVariable at h
cases h; case _ x h =>
cases h; case _ h1 h2 =>
  simp at h1

theorem hs_no_valid_head_variable_with_arrow :
  ¬ HsValidHeadVariable (A → B) test
:= by
intro h; unfold HsValidHeadVariable at h
cases h; case _ x h =>
cases h; case _ h1 h2 =>
  simp at h1


theorem hs_prefix_type_match_forced_refl :
  HsValidHeadVariable A Γ.is_stable ->
  PrefixHsTypeMatch Γ A B T ->
  B = T
:= by
intro j1 j2
cases j2
case _ => rfl
case _ =>
  exfalso
  apply hs_no_valid_head_variable_with_arrow j1
case _ =>
  exfalso
  apply hs_no_valid_head_variable_with_all j1

theorem hs_datatype_opent_distinct : ValidHsCtorType Γ T -> ValidHsInstType Γ T -> False := by
intros vctor vit;
cases vctor;
case refl h1 =>
  cases vit;
  case refl h2 =>
    unfold HsValidHeadVariable at h1; unfold HsValidHeadVariable at h2
    cases h1; case _ h1 =>
    cases h1; case _ tnf dt =>
    cases h2; case _ h2 =>
    cases h2; case _ tnf' ot =>
    rw[<-tnf] at tnf'; cases tnf'; simp at *;
    apply indexing_uniqueness_datatype dt ot;
  all_goals (
  case _ h2 =>
    cases h1;
    case _ ts h1 =>
      cases h1; case _ nf _ => cases nf;)
all_goals (
  case _ h1 =>
  cases vit;
  case refl h2 =>
    cases h2;
    case _ h2 =>
    cases h2; case _ nf _ => cases nf
  case _ h2 =>
    apply hs_datatype_opent_distinct h1 h2)
