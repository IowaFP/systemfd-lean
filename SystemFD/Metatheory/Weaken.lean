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
  unfold Ren.lift; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp
case _ x =>
  rw [Subst.lift_lemma]; simp
  unfold Ren.lift; simp
  rw [<-h x, Frame.apply_compose, Frame.apply_compose]; simp

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
case _ A t b T j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  replace ih1 := ih1 r wf h
  replace ih2 := ih2 r wf h
  have lem : ⊢ (Frame.term ([r.to]A) ([r.to]t) :: Δ) := by
    constructor; apply ih2; apply ih1; apply wf
  replace ih3 := @ih3 (Frame.term ([r.to]A) ([r.to]t) :: Δ) r.lift lem (rename_lift r (Frame.term A t) h)
  rw [Subst.lift_lemma] at ih3; simp at ih3
  constructor; apply ih2; apply ih1; simp; apply ih3
  apply ih4 r wf h
case _ => constructor; apply wf
case _ Γ x T j1 j2 ih =>
  unfold Ren.to; simp; constructor; apply wf
  rw [<-h x]; simp; rw [<-j2]; simp; unfold Ren.to; simp
case _ => constructor <;> simp [*]
case _ A B j1 j2 ih1 ih2 =>
  replace ih1 := ih1 r wf h
  have lem : ⊢ (Frame.kind ([r.to]A) :: Δ) := by
    constructor; apply ih1; apply wf
  replace ih2 := @ih2 (Frame.kind ([r.to]A) :: Δ) r.lift lem (rename_lift r (Frame.kind A) h)
  rw [Subst.lift_lemma] at ih2; simp at ih2
  constructor; apply ih1; apply ih2
case _ A B j1 j2 ih1 ih2 =>
  replace ih1 := ih1 r wf h
  have lem : ⊢ (Frame.empty :: Δ) := by
    constructor; assumption
  replace ih2 := @ih2 (Frame.empty :: Δ) r.lift lem (rename_lift r (.empty) h)
  rw [Subst.lift_lemma] at ih2; simp at ih2
  constructor; apply ih1; apply ih2
case _ ih1 ih2 =>
  constructor; apply ih2 r wf h
  apply ih1 r wf h
case _ ih1 ih2 ih3 =>
  constructor; apply ih3 r wf h
  apply ih1 r wf h; apply ih2 r wf h
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
case _ A t B j1 j2 j3 ih1 ih2 ih3 =>
  have lem1 := ih2 r wf h
  have lem2 : ⊢ (Frame.type ([r.to]A) :: Δ) := by
    constructor; assumption; assumption
  replace ih1 := @ih1 (Frame.type ([r.to]A) :: Δ) (Ren.lift r) lem2 (rename_lift r (.type A) h)
  rw [Subst.lift_lemma] at ih1; simp at ih1
  constructor; apply lem1; apply ih1; apply ih3 r wf h
case _ ih1 ih2 =>
  constructor; apply ih2 r wf h
  apply ih1 r wf h; simp [*]
case _ A t B j1 j2 j3 ih1 ih2 ih3 =>
  have lem1 := ih2 r wf h
  have lem2 : ⊢ (.kind ([r.to]A) :: Δ) := by
    constructor; apply lem1; apply wf
  replace ih1 := @ih1 (.kind ([r.to]A) :: Δ) (Ren.lift r) lem2 (rename_lift r (.kind A) h)
  rw [Subst.lift_lemma] at ih1; simp at ih1
  constructor; apply lem1; apply ih1; apply ih3 r wf h
case _ ih1 ih2 =>
  constructor; apply ih2 r wf h
  apply ih1 r wf h; simp [*]
case _ ih1 ih2 =>
  constructor; apply ih1 r wf h; apply ih2 r wf h
case _ ih1 ih2 =>
  constructor; apply ih2 r wf h; apply ih1 r wf h
case _ ih =>
  constructor; apply ih r wf h
case _ ih1 ih2 =>
  constructor; apply ih1 r wf h; apply ih2 r wf h
case _ ih1 ih2 =>
  constructor; apply ih1 r wf h; apply ih2 r wf h
case _ ih1 ih2 =>
  have lem1 : ⊢ (Frame.empty :: Δ) := by constructor; assumption
  replace ih2 := @ih2 (Frame.empty :: Δ) (Ren.lift r) lem1 (rename_lift r (Frame.empty) h)
  rw [Subst.lift_lemma] at ih2; simp at ih2
  constructor; apply ih1 r wf h; apply ih2
case _ ih1 ih2 ih3 =>
  constructor; apply ih1 r wf h
  apply ih2 r wf h; apply ih3 r wf h
case _ ih1 ih2 ih3 ih4 =>
  constructor; apply ih3 r wf h
  apply ih1 r wf h; apply ih2 r wf h
  apply ih4 r wf h
case _ K t A B j1 j2 ih1 ih2 =>
  have lem1 := ih1 r wf h
  have lem2 : ⊢ (.kind ([r.to]K) :: Δ) := by
    constructor; apply lem1; apply wf
  replace ih2 := @ih2 (.kind ([r.to]K) :: Δ) (Ren.lift r) lem2 (rename_lift r (.kind K) h)
  rw [Subst.lift_lemma] at ih2; simp at ih2
  constructor; apply lem1; apply ih2
case _ j1 j2 ih1 ih2 =>
  constructor; apply ih1 r wf h
  apply ih2 r wf h
  subst j1; simp
  subst j2; simp
case _ ih =>
  constructor; apply ih r wf h
case _ ih1 ih2 ih3 =>
  constructor; apply ih3 r wf h
  apply ih1 r wf h; apply ih2 r wf h

theorem weaken :
  ⊢ (f :: Γ) ->
  Γ ⊢ t : A ->
  (f::Γ) ⊢ ([S]t) : ([S]A)
:= by
intro j1 j2; apply rename _ j2
case _ => apply j1
case _ => intro x; simp; rw [Subst.to_S]

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
  ValidCtorType Γ T ->
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
  (.inst #x b::Γ) ⊢ ([S]t) : ([S]A)
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
