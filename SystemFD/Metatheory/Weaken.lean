import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.TypeMatch

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
case _ Γ T t A j1 j2 ih1 ih2 => sorry
  -- replace ih2 := ih2 r wf h
  -- have lem : ⊢ (Frame.datatype ([r.to]T) :: Δ) := by
  --   constructor; apply ih2; apply wf
  -- replace ih1 := @ih1 (Frame.datatype ([r.to]T) :: Δ) r.lift lem (rename_lift r (Frame.datatype T) h)
  -- rw [Subst.lift_lemma] at ih1; simp at ih1
  -- constructor; apply ih2; apply ih1
case _ => constructor; apply wf
case _ Γ x T j1 j2 ih =>
  unfold Ren.to; simp; constructor; apply wf
  rw [<-h x]; simp; rw [<-j2]; simp; unfold Ren.to; simp
case _ => constructor <;> simp [*]
case _ =>
  -- replace ih2 := ih2 r wf h
  -- replace ih3 := ih3 r wf h
  -- have lem : ⊢ (Frame.kind ([r.to]A) :: Δ) := by sorry
  -- replace ih1 := @ih1 (Frame.kind ([r.to]A) :: Δ) r.lift lem (rename_lift r (Frame.kind A) h)
  -- rw [Subst.lift_lemma] at ih1; simp at ih1
  -- constructor; apply ih2; apply ih1
  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
  constructor; apply ih1 r wf h; apply ih2 r wf h
  apply ih5 r wf h; apply ih3 r wf h
  apply valid_head_variable_subst _ _ _ j5
  intro n h1; unfold Ren.to; simp at h1; simp; rw [<-h n]
  rw [Frame.is_ctor_stable]; apply h1
  apply valid_head_variable_subst _ _ _ j6
  intro n h1; unfold Ren.to; simp at h1; simp; rw [<-h n]
  rw [Frame.is_datatype_stable]; apply h1
  apply stable_type_match_subst _ _ j7
  intro n y h1; unfold Ren.to at h1; simp at h1; rw [<-h1]; apply h n
  intro n h1; unfold Ren.to; simp
  apply prefix_type_match_subst _ _ j8
  intro n y h1; unfold Ren.to at h1; simp at h1; rw [<-h1]; apply h n
  intro n h1; unfold Ren.to; simp
  apply ih6 r wf h; apply ih4 r wf h
case _ j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
  constructor; apply ih1 r wf h; apply ih2 r wf h
  apply ih4 r wf h; apply ih3 r wf h
  apply valid_head_variable_subst _ _ _ j5
  intro n h1; unfold Ren.to; simp at h1; simp; rw [<-h n]
  rw [Frame.is_insttype_stable]; apply h1
  apply valid_head_variable_subst _ _ _ j6
  intro n h1; unfold Ren.to; simp at h1; simp; rw [<-h n]
  rw [Frame.is_opent_stable]; apply h1
  apply stable_type_match_subst _ _ j7
  intro n y h1; unfold Ren.to at h1; simp at h1; rw [<-h1]; apply h n
  intro n h1; unfold Ren.to; simp
  apply prefix_type_match_subst _ _ j8
  intro n y h1; unfold Ren.to at h1; simp at h1; rw [<-h1]; apply h n
  intro n h1; unfold Ren.to; simp
  apply ih5 r wf h
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
  Γ ⊢ T : ★ ->
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
  ValidCtor Γ T ->
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
  Γ ⊢ T : ★ ->
  Γ ⊢ t : A ->
  (.openm T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => constructor; apply j1; apply judgment_ctx_wf j1
case _ => intro x; simp; rw [Subst.to_S]

theorem weaken_insttype :
  Γ ⊢ T : ★ ->
  ValidInstType Γ T ->
  Γ ⊢ t : A ->
  (.insttype T::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2 j3; apply rename _ j3
case _ => constructor; apply j1; apply judgment_ctx_wf j1; apply j2
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
  Γ ⊢ T : ★ ->
  Γ ⊢ b : T ->
  Γ ⊢ t : A ->
  (.term T b::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2 j3; apply rename _ j3
case _ => constructor; apply j1; apply j2; apply judgment_ctx_wf j2
case _ => intro x; simp; rw [Subst.to_S]
