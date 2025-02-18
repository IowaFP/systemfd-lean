import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

-- theorem lift_subst_rename (A : Term) :
--   (∀ n y, σ n = .re y -> [σ](Γ d@ n) = Δ d@ y) ->
--   (∀ n y, ^σ n = .re y -> [^σ]((A :: Γ) d@ n) = ([σ]A :: Δ) d@ y)
-- := by
-- intro h1 n y h2
-- cases n
-- case _ => simp at *; subst h2; simp
-- case _ n =>
--   simp at *; unfold Subst.compose at h2; simp at h2
--   generalize ydef : σ n = y at *
--   cases y <;> simp at h2
--   case _ z =>
--     subst h2; simp
--     replace h1 := h1 n z ydef
--     rw [<-Term.apply_compose, h1]

-- theorem lift_subst_replace :
--   Δ ⊢ ([σ]A) : .const K ->
--   (∀ n t, σ n = .su t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
--   (∀ n t, ^σ n = .su t -> ([σ]A :: Δ) ⊢ t : ([^σ](A :: Γ) d@ n))
-- := by
-- intro j h1 n t h2
-- cases n <;> simp at *
-- case _ n =>
--   unfold Subst.compose at h2; simp at h2
--   generalize ydef : σ n = y at *
--   cases y <;> simp at h2
--   case _ t' =>
--     replace h1 := h1 n t' ydef
--     subst h2
--     rw [<-Term.apply_compose]
--     apply weaken; apply j; apply h1

@[simp]
abbrev idx_subst (σ : Subst Term) : JudgmentArgs v -> JudgmentArgs v :=
  match v with
  | .prf => λ (t, A) => ([σ]t, [σ]A)
  | .wf => λ () => ()

theorem subst :
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  Judgment v Γ idx ->
  ⊢ Δ ->
  Judgment v Δ (idx_subst σ idx)
:= by
intro h1 h2 h3 j wf
induction j generalizing Δ σ
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
case _ => sorry
case _ => sorry

theorem beta_empty t :
  (.empty::Γ) ⊢ b : B ->
  Γ ⊢ (b β[t]) : (B β[t])
:= by
intro j
have lem : ⊢ Γ := by
  have lem := judgment_ctx_wf j
  cases lem; simp [*]
apply @subst (.su t :: I) (.empty::Γ) Γ _ _ _ _ _ j
apply lem
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1

theorem beta_type :
  (.type A::Γ) ⊢ b : B ->
  Γ ⊢ t : A ->
  Γ ⊢ (b β[t]) : (B β[t])
:= by
intro j1 j2
apply @subst (.su t :: I) (.type A::Γ) Γ _ _ _ _ _ j1
apply judgment_ctx_wf j2
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e; simp
  apply j2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1

theorem beta_kind :
  (.kind A::Γ) ⊢ b : B ->
  Γ ⊢ t : A ->
  Γ ⊢ (b β[t]) : (B β[t])
:= by
intro j1 j2
apply @subst (.su t :: I) (.kind A::Γ) Γ _ _ _ _ _ j1
apply judgment_ctx_wf j2
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e; simp
  apply j2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1

theorem beta_term :
  (.term A t::Γ) ⊢ b : B ->
  Γ ⊢ t : A ->
  Γ ⊢ (b β[t]) : (B β[t])
:= by
intro j1 j2
apply @subst (.su t :: I) (.term A t::Γ) Γ _ _ _ _ _ j1
apply judgment_ctx_wf j2
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e; simp
  apply j2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1

theorem beta_openm :
  (.openm A::Γ) ⊢ b : B ->
  Γ ⊢ t : A ->
  Γ ⊢ (b β[t]) : (B β[t])
:= by
intro j1 j2
apply @subst (.su t :: I) (.openm A::Γ) Γ _ _ _ _ _ j1
apply judgment_ctx_wf j2
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e; simp
  apply j2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1
