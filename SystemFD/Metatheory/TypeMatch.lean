import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

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

theorem stable_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, (Γ d@ n).is_stable -> ∃ y, σ n = .re y) ->
  StableTypeMatch Γ A B ->
  StableTypeMatch Δ ([σ]A) ([σ]B)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ sp Γ x R j1 j2 =>
  replace h2 := h2 x j2
  cases h2; case _ y h2 =>
    replace j1 := neutral_form_subst σ h2 (Eq.symm j1); simp at j1
    constructor; rw [j1]; rw [<-h1 x y h2, Frame.is_stable_stable]
    apply j2
case _ Γ A B R j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.type A).apply σ) :: Δ)
    (lift_subst_rename (Frame.type A) h1)
    (lift_subst_stable (Frame.type A) h2)
  simp at ih; apply ih
case _ Γ A B R j ih =>
  simp; constructor; simp
  replace ih := @ih (^σ)
    (((Frame.kind A).apply σ) :: Δ)
    (lift_subst_rename (Frame.kind A) h1)
    (lift_subst_stable (Frame.kind A) h2)
  simp at ih; apply ih

theorem prefix_type_match_subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, (Γ d@ n).is_stable -> ∃ y, σ n = .re y) ->
  PrefixTypeMatch Γ A B T ->
  PrefixTypeMatch Δ ([σ]A) ([σ]B) ([σ]T)
:= by
intro h1 h2 j
induction j generalizing Δ σ
case _ sp Γ x B T j1 j2 =>
  replace h2 := h2 x j2
  cases h2; case _ y h2 =>
    replace j1 := neutral_form_subst σ h2 (Eq.symm j1); simp at j1
    constructor; rw [j1]; rw [<-h1 x y h2, Frame.is_stable_stable]
    apply j2
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
