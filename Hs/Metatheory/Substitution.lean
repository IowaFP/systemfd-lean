import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken

set_option maxHeartbeats 500000

def hs_lift_subst_replace_type (A : Frame HsTerm) :
  ⊢s (A.apply σ :: Δ) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢τ t : ([σ]T)) ->
  (∀ n t T, ^σ n = .su t -> .some T = ((A::Γ) d@ n).get_type -> (A.apply σ :: Δ) ⊢τ t : ([^σ]T))
:= by
intro j h1 n t T h2 h3;
cases n <;> simp at *;
case _ n =>
  unfold Subst.compose at h2; simp at h2
  generalize ydef : σ n = y at *;
  cases y <;> simp at h2
  case _ t' =>
    subst h2
    have lem : Option.map ([P]·) (some T) = (Γ d@ n).get_type := by
      rw [h3]; simp; unfold Function.comp; simp
    simp at lem
    replace h1 := h1 n t' ([P]T) ydef lem
    have lem2 : ∃ T', T = [S]T' := by
      generalize wdef : (Γ d@ n).get_type = w at *
      cases w
      case _ => cases lem
      case _ T' => simp at h3; exists T'
    have lem3 : [S ⊙ σ ⊙ P]T = [^σ]T := by
      cases lem2; case _ T' lem2 =>
      subst lem2; simp; rw [<-Subst.assoc]
      rw [Subst.P_after_S]; simp
    have lem4 := hs_weaken_type j h1; simp at lem4
    rw [lem3] at lem4; simp at lem4
    apply lem4

def hs_lift_subst_replace (A : Frame HsTerm) :
  ⊢s (A.apply σ :: Δ) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢t t : ([σ]T)) ->
  (∀ n t T, ^σ n = .su t -> .some T = ((A::Γ) d@ n).get_type -> (A.apply σ :: Δ) ⊢t t : ([^σ]T))
:= by
intro j h1 n t T h2 h3
cases n <;> simp at *
case _ n =>
  unfold Subst.compose at h2; simp at h2
  generalize ydef : σ n = y at *
  cases y <;> simp at h2
  case _ t' =>
    subst h2
    have lem : Option.map ([P]·) (some T) = (Γ d@ n).get_type := by
      rw [h3]; simp; unfold Function.comp; simp
    simp at lem
    replace h1 := h1 n t' ([P]T) ydef lem
    have lem2 : ∃ T', T = [S]T' := by
      generalize wdef : (Γ d@ n).get_type = w at *
      cases w
      case _ => cases lem
      case _ T' => simp at h3; exists T'
    have lem3 : [S ⊙ σ ⊙ P]T = [^σ]T := by
      cases lem2; case _ T' lem2 =>
      subst lem2; simp; rw [<-Subst.assoc]
      rw [Subst.P_after_S]; simp
    have lem4 := hs_weaken_term j h1; simp at lem4
    rw [lem3] at lem4; simp at lem4
    apply lem4

@[simp]
abbrev hs_idx_subst (σ : Subst HsTerm) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .term => λ (t, A) => ([σ]t, [σ]A)
  | .kind => λ (t, A) => ([σ]t, [σ]A)
  | .type => λ (t, A) => ([σ]t, [σ]A)
  | .ctx => λ () => ()

def hs_subst : (v: HsVariant) -> {idx : HsJudgmentArgs v} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢τ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  HsJudgment v Δ (hs_idx_subst σ idx)
| .ctx, (),  f1, f2, f3, j, wf => wf
| .kind, (t, τ), f1, f2, f3, j, wf => match j with
  | .ax wf' => by constructor; assumption
  | .arrowk h1 h2 => by
    have lem1 := hs_subst .kind f1 f2 f3 h1 wf; simp at lem1
    have lem2 := hs_subst .kind f1 f2 f3 h2 wf; simp at lem2
    simp; constructor; assumption; assumption;
| .type, (t, τ), f1, f2, f3, j, wf => match j with
  | @HsJudgment.varTy Γ x T h1 h2 h3 h4 => by
    simp;
    generalize zdef : σ x = z at *;
    cases z <;> simp
    case _ y =>
      have lem1 := f1 x y zdef
      have lem2 := f2 x
      have lem3 := hs_subst .kind f1 f2 f3 h4 wf
      apply HsJudgment.varTy;
      apply wf
      rw[<-lem1]; simp;
      simp at h2; cases h2;
      case _ h =>
        have u := datatype_indexing_exists h;
        cases u; case _ u =>
        apply Or.inl;
        rw[u]; unfold Frame.apply; simp; unfold Frame.is_datatype; simp
      case _ h =>
        have u := kind_indexing_exists h;
        cases u; case _ u =>
        apply Or.inr;
        rw[u]; unfold Frame.apply; simp; unfold Frame.is_kind; simp
      case _ =>
        rw[<-lem1]; rw[Frame.get_type_apply_commute]; rw[<-h3]; simp;
      apply lem3
    case _ a =>
      have lem := f2 x a T  zdef h3
      apply lem

  | .appk h1 h2 h3 h4 => by
     have lem1 := hs_subst .type f1 f2 f3 h1 wf
     have lem2 := hs_subst .type f1 f2 f3 h2 wf
     have lem3 := hs_subst .kind f1 f2 f3 h3 wf
     have lem4 := hs_subst .kind f1 f2 f3 h4 wf
     apply HsJudgment.appk;
     assumption; assumption; assumption; assumption

  | @HsJudgment.farrow Γ A B h1 h2 h3 => by
    have lem1 := hs_subst .type f1 f2 f3 h1 wf
    have lem2 : HsValidHeadVariable ([σ]A) Δ.is_opent := by
      apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent
      case _ =>
        intro n t;
        exists n; apply And.intro;
        sorry
        sorry
      apply h2
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have lem3 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply hs_subst .type _ _ _ h3 wf'
      case _ => apply hs_lift_subst_rename .empty f1
      case _ => apply hs_lift_subst_replace_type .empty wf' f2
      case _ => apply hs_lift_subst_stable .empty f3
    apply HsJudgment.farrow;
    apply lem1
    apply lem2
    apply lem3

  | @HsJudgment.allt Γ A B h1 h2 => by
    have lem1 := hs_subst .kind f1 f2 f3 h1 wf
    have wf' : ⊢s (Frame.kind ([σ]A) :: Δ) := by
      constructor; assumption; assumption
    have u1 := hs_lift_subst_rename (.kind A) f1
    have u2 := hs_lift_subst_replace_type (.kind A) wf' f2
    have u3 := hs_lift_subst_stable (.kind A) f3

    have lem2 : (Frame.kind ([σ]A) :: Δ) ⊢τ ([^σ]B) : `★ := by
      apply hs_subst .type _ _ _ h2 wf'
      case _ => assumption
      case _ => assumption
      case _ => assumption
    constructor; assumption; assumption

  | @HsJudgment.arrow Γ A B h1 h2 => by
    have lem1 := hs_subst .type f1 f2 f3 h1 wf
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have lem2 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply hs_subst .type _ _ _ h2 wf'
      case _ => apply hs_lift_subst_rename .empty f1
      case _ => apply hs_lift_subst_replace_type .empty wf' f2
      case _ => apply hs_lift_subst_stable .empty f3
    apply HsJudgment.arrow;
    apply lem1
    apply lem2

| .term, (t, τ), f1, f2, f3, j, wf => match j with
  | @HsJudgment.implicitAllI Γ A t τ h1 h2 => by sorry

  | @HsJudgment.implicitArrI Γ π τ t h1 h2 h3 h4 => by sorry

  | @HsJudgment.implicitAllE Γ A τ t e τ' h1 h2 h3 h4 h5 => by sorry

  | @HsJudgment.implicitArrE Γ t π τ e τ' h1 h2 h3 h4 => by sorry

  | @HsJudgment.var Γ x T wf' test gt => by sorry

  | @HsJudgment.lam Γ A t B h1 h2 h3 => by sorry

  | @HsJudgment.app Γ t1 A B t2 B' h1 h2 h3 h4 h5 => by sorry

  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by sorry

  | @HsJudgment.hslet Γ A t1 B' B t2 h1 h2 h3 h4 h5 => by sorry
termination_by _ _ _ _ _ h => h.size
-- induction j generalizing Δ σ
-- any_goals (solve | apply wf)
-- case letterm A t b T j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
--   simp at *
--   have lem1 := ih1 h1 h2 h3 wf
--   have lem2 := ih2 h1 h2 h3 wf
--   have lem3 : ⊢s ((Frame.term A t).apply σ :: Δ) := by
--     apply Judgment.wfterm lem1 lem2 wf
--   replace ih3 := @ih3 (^σ) ((Frame.term A t).apply σ :: Δ)
--     (lift_subst_rename (Frame.term A t) h1)
--     (lift_subst_replace (Frame.term A t) lem3 h2)
--     (lift_subst_stable (Frame.term A t) h3)
--     lem3
--   simp at ih3
--   apply Judgment.letterm lem1 lem2
--   simp; apply ih3; apply ih4 h1 h2 h3 wf
-- case ax ih =>
--   simp at *
--   apply Judgment.ax wf
-- case var Γ x T j1 j2 ih =>
--   simp at *
--   generalize zdef : σ x = z at *
--   cases z <;> simp
--   case _ y =>
--     constructor; apply wf; rw [<-h1 _ _ zdef]
--     rw [Frame.get_type_apply_commute, <-j2]; simp
--   case _ t => apply h2 x _ _ zdef j2
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.allk ih1 ih2
-- case _ Γ A B j1 j2 ih1 ih2 =>
--   simp at *
--   have lem := ih1 h1 h2 h3 wf
--   have lem2 : ⊢s ((Frame.kind A).apply σ :: Δ) := by
--     apply Judgment.wfkind lem wf
--   replace ih2 := @ih2 (^σ) ((Frame.kind A).apply σ :: Δ)
--     (lift_subst_rename (Frame.kind A) h1)
--     (lift_subst_replace (Frame.kind A) lem2 h2)
--     (lift_subst_stable (Frame.kind A) h3)
--     lem2
--   simp at ih2
--   constructor; apply lem; apply ih2
-- case _ A _ _ _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   have lem2 : ⊢s ((Frame.empty).apply σ :: Δ) := by
--     constructor; assumption
--   replace ih2 := @ih2 (^σ) ((Frame.empty).apply σ :: Δ)
--     (lift_subst_rename (Frame.empty) h1)
--     (lift_subst_replace (Frame.empty) lem2 h2)
--     (lift_subst_stable (Frame.empty) h3)
--     lem2
--   simp at ih2
--   apply Judgment.arrow ih1 ih2
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.appk ih1 ih2
-- case _ ih1 ih2 ih3 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   apply Judgment.eq ih1 ih2 ih3
-- case ite Γ p A s R i B T e j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 ih1 ih2 ih3 ih4 ih5 ih6 =>
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   replace ih4 := ih4 h1 h2 h3 wf
--   replace ih5 := ih5 h1 h2 h3 wf
--   replace ih6 := ih6 h1 h2 h3 wf
--   replace j7 := stable_type_match_subst h1 h3 j7
--   replace j8 := prefix_type_match_subst h1 h3 j8
--   apply Judgment.ite ih1 ih2 ih3 ih4 _ _ j7 j8 ih5 ih6
--   case _ =>
--     apply valid_head_variable_subst Γ.is_ctor Δ.is_ctor _ j5
--     intro n h
--     have lem : Γ.is_stable n := by
--       apply Frame.is_ctor_implies_is_stable h
--     replace h3 := h3 n lem
--     cases h3; case _ y h3 =>
--     apply Exists.intro y; apply And.intro h3
--     replace h1 := h1 _ _ h3
--     simp at h; simp; rw [<-@Frame.is_ctor_stable _ _ σ _] at h
--     rw [h1] at h; apply h
--   case _ =>
--     apply valid_head_variable_subst Γ.is_datatype Δ.is_datatype _ j6
--     intro n h
--     have lem : Γ.is_stable n := by
--       apply Frame.is_datatype_implies_is_stable h
--     replace h3 := h3 n lem
--     cases h3; case _ y h3 =>
--     apply Exists.intro y; apply And.intro h3
--     replace h1 := h1 _ _ h3
--     simp at h; simp; rw [<-@Frame.is_datatype_stable _ _ σ _] at h
--     rw [h1] at h; apply h
-- case guard Γ p A s R t B T j1 j2 j3 j4 j5 j6 j7 j8 j9 ih1 ih2 ih3 ih4 ih5 =>
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   replace ih4 := ih4 h1 h2 h3 wf
--   replace ih5 := ih5 h1 h2 h3 wf
--   replace j7 := stable_type_match_subst h1 h3 j7
--   replace j8 := prefix_type_match_subst h1 h3 j8
--   apply Judgment.guard ih1 ih2 ih3 ih4 _ _ j7 j8 ih5
--   case _ =>
--     apply valid_head_variable_subst Γ.is_insttype Δ.is_insttype _ j5
--     intro n h
--     have lem : Γ.is_stable n := by
--       apply Frame.is_insttype_implies_is_stable h
--     replace h3 := h3 n lem
--     cases h3; case _ y h3 =>
--     apply Exists.intro y; apply And.intro h3
--     replace h1 := h1 _ _ h3
--     simp at h; simp; rw [<-@Frame.is_insttype_stable _ _ σ _] at h
--     rw [h1] at h; apply h
--   case _ =>
--     apply valid_head_variable_subst Γ.is_opent Δ.is_opent _ j6
--     intro n h
--     have lem : Γ.is_stable n := by
--       apply Frame.is_opent_implies_is_stable h
--     replace h3 := h3 n lem
--     cases h3; case _ y h3 =>
--     apply Exists.intro y; apply And.intro h3
--     replace h1 := h1 _ _ h3
--     simp at h; simp; rw [<-@Frame.is_opent_stable _ _ σ _] at h
--     rw [h1] at h; apply h
-- case _ Γ A t B j1 j2 j3 ih1 ih2 ih3 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   have lem2 : ⊢s ((Frame.type A).apply σ :: Δ) := by
--     constructor; assumption; assumption
--   replace ih2 := @ih2 (^σ) ((Frame.type A).apply σ :: Δ)
--     (lift_subst_rename (Frame.type A) h1)
--     (lift_subst_replace (Frame.type A) lem2 h2)
--     (lift_subst_stable (Frame.type A) h3)
--     lem2
--   simp at ih2
--   apply Judgment.lam ih1 ih2 ih3
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.app ih1 ih2; simp [*]
-- case _ Γ A t B j1 j2 j3 ih1 ih2 ih3 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   have lem2 : ⊢s ((Frame.kind A).apply σ :: Δ) := by
--     apply Judgment.wfkind ih1 wf
--   replace ih2 := @ih2 (^σ) ((Frame.kind A).apply σ :: Δ)
--     (lift_subst_rename (Frame.kind A) h1)
--     (lift_subst_replace (Frame.kind A) lem2 h2)
--     (lift_subst_stable (Frame.kind A) h3)
--     lem2
--   simp at ih2
--   apply Judgment.lamt ih1 ih2 ih3
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.appt ih1 ih2; simp [*]
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.cast ih1 ih2
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.refl ih1 ih2
-- case _ ih =>
--   simp at *
--   replace ih := ih h1 h2 h3 wf
--   apply Judgment.sym ih
-- case _ ih1 ih2 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   apply Judgment.seq ih1 ih2
-- case _ ih1 ih2 ih3 ih4 ih5 ih6 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   replace ih4 := ih4 h1 h2 h3 wf
--   replace ih5 := ih5 h1 h2 h3 wf
--   replace ih6 := ih6 h1 h2 h3 wf
--   apply Judgment.appc ih1 ih2 ih3 ih4 ih5 ih6
-- case _ A B _ _ _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   have lem1 : ⊢s ((Frame.empty).apply σ :: Δ) := by constructor; assumption;
--   replace ih4 := @ih4 (^σ) ((Frame.empty).apply σ :: Δ)
--     (lift_subst_rename (Frame.empty) h1)
--     (lift_subst_replace (Frame.empty) lem1 h2)
--     (lift_subst_stable (Frame.empty) h3)
--     lem1
--   simp at ih4
--   replace ih5 := @ih5 (^σ) ((Frame.empty).apply σ :: Δ)
--     (lift_subst_rename (Frame.empty) h1)
--     (lift_subst_replace (Frame.empty) lem1 h2)
--     (lift_subst_stable (Frame.empty) h3)
--     lem1
--   simp at ih5
--   replace ih6 := @ih6 (^σ) ((Frame.empty).apply σ :: Δ)
--     (lift_subst_rename (Frame.empty) h1)
--     (lift_subst_replace (Frame.empty) lem1 h2)
--     (lift_subst_stable (Frame.empty) h3)
--     lem1
--   simp at ih6
--   apply Judgment.arrowc ih1 ih2 ih3 ih4 ih5 ih6
-- case _ ih1 ih2 ih3 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   apply Judgment.fst ih1 ih2 ih3
-- case _ ih1 ih2 ih3 ih4 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   replace ih4 := ih4 h1 h2 h3 wf
--   apply Judgment.snd ih1 ih2 ih3 ih4
-- case _ Γ K A B t j1 j2 j3 ih1 ih2 ih3 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   have lem2 : ⊢s ((Frame.kind K).apply σ :: Δ) := by
--     cases ih1; case _ ih1 _ =>
--       apply Judgment.wfkind ih1 wf
--   replace ih3 := @ih3 (^σ) ((Frame.kind K).apply σ :: Δ)
--     (lift_subst_rename (Frame.kind K) h1)
--     (lift_subst_replace (Frame.kind K) lem2 h2)
--     (lift_subst_stable (Frame.kind K) h3)
--     lem2
--   simp at ih3
--   apply Judgment.allc ih1 ih2 ih3
-- case _ ih1 ih2 ih3 ih4 =>
--   simp at *
--   replace ih1 := ih1 h1 h2 h3 wf
--   replace ih2 := ih2 h1 h2 h3 wf
--   replace ih3 := ih3 h1 h2 h3 wf
--   replace ih4 := ih4 h1 h2 h3 wf
--   apply Judgment.apptc ih1 ih2 ih3 ih4
--   simp [*]; simp [*]

def hs_beta_empty_type t :
  (.empty::Γ) ⊢τ b : B ->
  Γ ⊢τ (b β[t]) : (B β[t])
:= by sorry


def hs_beta_empty_term t :
  (.empty::Γ) ⊢t b : B ->
  Γ ⊢t (b β[t]) : (B β[t])
:= by sorry
-- intro j
-- have lem : ⊢t Γ := by
--   have lem := hs_judgment_ctx_wf .prf j
--   cases lem;
-- apply @subst (.su t :: I) (.empty::Γ) Γ _ _ _ _ _ j
-- apply lem
-- case _ =>
--   intro n y h1
--   cases n <;> simp at *; subst h1
--   case _ n =>
--     rw [Frame.apply_compose]; simp
-- case _ =>
--   intro n s T h1 h2
--   cases n <;> simp at *; subst h1
--   injection h2
-- case _ =>
--   intro n h1
--   cases n <;> simp at *
--   rw [Frame.is_stable_stable] at h1
--   unfold Frame.is_stable at h1
--   simp at h1

def hs_beta_type :
  (.type A::Γ) ⊢t b : B ->
  Γ ⊢t t : A ->
  Γ ⊢t (b β[t]) : (B β[t])
:= by sorry
-- intro j1 j2
-- apply @subst (.su t :: I) (.type A::Γ) Γ _ _ _ _ _ j1
-- apply judgment_ctx_wf j2
-- case _ =>
--   intro n y h1
--   cases n <;> simp at *; subst h1
--   case _ n =>
--     rw [Frame.apply_compose]; simp
-- case _ =>
--   intro n s T h1 h2
--   cases n <;> simp at *; subst h1
--   injection h2 with e; subst e; simp
--   apply j2
-- case _ =>
--   intro n h1
--   cases n <;> simp at *
--   rw [Frame.is_stable_stable] at h1
--   unfold Frame.is_stable at h1
--   simp at h1

def hs_beta_kind :
  (.kind A::Γ) ⊢t b : B ->
  Γ ⊢t t : A ->
  Γ ⊢t (b β[t]) : (B β[t])
:= by sorry

def hs_beta_kind_type :
  (.kind A::Γ) ⊢τ b : B ->
  Γ ⊢τ t : A ->
  Γ ⊢τ (b β[t]) : (B β[t])
:= by sorry

-- intro j1 j2
-- apply @subst (.su t :: I) (.kind A::Γ) Γ _ _ _ _ _ j1
-- apply judgment_ctx_wf j2
-- case _ =>
--   intro n y h1
--   cases n <;> simp at *; subst h1
--   case _ n =>
--     rw [Frame.apply_compose]; simp
-- case _ =>
--   intro n s T h1 h2
--   cases n <;> simp at *; subst h1
--   injection h2 with e; subst e; simp
--   apply j2
-- case _ =>
--   intro n h1
--   cases n <;> simp at *
--   rw [Frame.is_stable_stable] at h1
--   unfold Frame.is_stable at h1
--   simp at h1

def hs_beta_term :
  (.term A t::Γ) ⊢t b : B ->
  Γ ⊢t t : A ->
  Γ ⊢t (b β[t]) : (B β[t])
:= by sorry
-- intro j1 j2
-- apply @subst (.su t :: I) (.term A t::Γ) Γ _ _ _ _ _ j1
-- apply judgment_ctx_wf j2
-- case _ =>
--   intro n y h1
--   cases n <;> simp at *; subst h1
--   case _ n =>
--     rw [Frame.apply_compose]; simp
-- case _ =>
--   intro n s T h1 h2
--   cases n <;> simp at *; subst h1
--   injection h2 with e; subst e; simp
--   apply j2
-- case _ =>
--   intro n h1
--   cases n <;> simp at *
--   rw [Frame.is_stable_stable] at h1
--   unfold Frame.is_stable at h1
--   simp at h1

def hs_beta_openm :
  (.openm A::Γ) ⊢t b : B ->
  Γ ⊢t t : A ->
  Γ ⊢t (b β[t]) : (B β[t])
:= by sorry
-- intro j1 j2
-- apply @subst (.su t :: I) (.openm A::Γ) Γ _ _ _ _ _ j1
-- apply judgment_ctx_wf j2
-- case _ =>
--   intro n y h1
--   cases n <;> simp at *; subst h1
--   case _ n =>
--     rw [Frame.apply_compose]; simp
-- case _ =>
--   intro n s T h1 h2
--   cases n <;> simp at *; subst h1
--   injection h2 with e; subst e; simp
--   apply j2
-- case _ =>
--   intro n h1
--   cases n <;> simp at *
--   rw [Frame.is_stable_stable] at h1
--   unfold Frame.is_stable at h1
--   simp at h1


def hs_replace_empty : (v : HsVariant) ->  {idx : HsJudgmentArgs v} ->
  HsJudgment v (.empty :: Γ) idx ->
  Γ ⊢τ A : `★ ->
  HsJudgment v (.type A :: Γ) idx
| .ctx, () , j, j' => by
  cases j; constructor; assumption; assumption
| .kind, (t, τ), j, j' => match j with
  | .ax h => by apply HsJudgment.ax; cases h; case _ h => apply HsJudgment.wftype; assumption; assumption
  | .arrowk h1 h2 => by apply HsJudgment.arrowk (hs_replace_empty .kind h1 j') (hs_replace_empty .kind h2 j')
| .type, (t, τ), j, j' => sorry
| .term, (t, τ), j, j' => sorry
termination_by _ _ h => h.size


def hs_replace_empty_type :
  Γ ⊢τ A : `★ ->
  (.empty :: Γ) ⊢τ B : `★ ->
  (.type A :: Γ) ⊢τ B : `★
:= λ a b => hs_replace_empty .type b a
