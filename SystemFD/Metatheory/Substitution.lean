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
  (∀ n t, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢ t : ([σ]T)) ->
  Judgment v Γ idx ->
  ⊢ Δ ->
  Judgment v Δ (idx_subst σ idx)
:= by
intro h1 h2 j wf
induction j generalizing Δ σ <;> simp at *
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
case _ Γ p A τ sR R s t B τ' sT ξ sT' T K j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 ih1 ih2 ih3 ih4 ih5 =>
  apply @Judgment.guard Δ ([σ]p) ([σ]A) (τ.apply σ) ([σ]sR) ([σ]R) ([σ]s) ([σ]t) ([σ]B)
    (τ'.apply σ) ([σ]sT) ξ ([σ]sT') ([σ]T) K
  apply ih1 h1 h2 wf
  sorry
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
