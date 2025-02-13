import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

theorem rename_lift r (A : Frame Term) :
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  ∀ x, ((A::Γ) d@ x).apply r.lift.to = (A.apply r.to::Δ) d@ (Ren.lift r x)
:= by
intro h x; simp
cases x <;> simp at *
case _ =>
  rw [Subst.lift_lemma]; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp
case _ x =>
  rw [Subst.lift_lemma, <-h x]; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp


@[simp]
abbrev idx_ren (r : Ren) : JudgmentArgs v -> JudgmentArgs v :=
  match v with
  | .prf => λ (t, A) => ([r.to]t, [r.to]A)
  | .wf => λ () => ()

theorem rename (r : Ren) :
  Judgment v Γ idx ->
  ⊢ Δ ->
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  Judgment v Δ (idx_ren r idx)
:= by
intro j wf h
induction j generalizing Δ r <;> simp at *
any_goals apply wf
case _ Γ T t A j1 j2 ih1 ih2 =>
  replace ih2 := ih2 r wf h
  have lem : ⊢ (Frame.datatype ([r.to]T) :: Δ) := by
    constructor; apply ih2; apply wf
  replace ih1 := @ih1 (Frame.datatype ([r.to]T) :: Δ) r.lift lem (rename_lift r (Frame.datatype T) h)
  rw [Subst.lift_lemma] at ih1; simp at ih1
  constructor; apply ih2; apply ih1
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
  sorry
  -- apply @Judgment.guard Δ ([r.to]p) ([r.to]A) τ ([r.to]sR) ([r.to]R) ([r.to]s) ([r.to]t)
  --   ([r.to]B) τ' ([r.to]sT) ξ ([r.to]sT') ([r.to]T) K
  -- apply ih1 r wf h
  -- sorry
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

theorem weaken_empty :
  Γ ⊢ t : A ->
  (.empty::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j; apply rename _ j
case _ => constructor; apply judgment_ctx_wf j
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_type :
  Γ ⊢ T : .const K ->
  Γ ⊢ t : A ->
  (.type T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_kind :
  Γ ⊢ T : .kind ->
  Γ ⊢ t : A ->
  (.kind T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_datatype :
  Γ ⊢ T : .kind ->
  Γ ⊢ t : A ->
  (.datatype T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_ctor :
  Γ ⊢ T : ★ ->
  valid_ctor Γ ->
  Γ ⊢ t : A ->
  (.ctor T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2 j3; apply rename _ j3
case _ => constructor; apply j1; apply judgment_ctx_wf j1; apply j2
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_opent :
  Γ ⊢ T : .kind ->
  Γ ⊢ t : A ->
  (.opent T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_openm :
  Γ ⊢ T : .const K ->
  Γ ⊢ t : A ->
  (.openm T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_insttype :
  Γ ⊢ T : .const K ->
  Γ ⊢ t : A ->
  (.openm T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_inst :
  .openm T = Γ d@ x ->
  Γ ⊢ b : T ->
  Γ ⊢ t : A ->
  (.inst x b::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2 j3; apply rename _ j3
case _ => constructor; apply j1; apply j2; apply judgment_ctx_wf j2
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_term :
  Γ ⊢ T : .const K ->
  Γ ⊢ b : T ->
  Γ ⊢ t : A ->
  (.term T b::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2 j3; apply rename _ j3
case _ => constructor; apply j1; apply j2; apply judgment_ctx_wf j2
case _ => intro x; simp; rw [Subst.to_S]
