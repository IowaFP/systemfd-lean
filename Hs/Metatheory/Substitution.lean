import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken

set_option maxHeartbeats 1000000

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

def hs_lift_subst_replace_term (A : Frame HsTerm) :
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

theorem subst_valid [SubstitutionType T][SubstitutionTypeLaws T] {σ : Subst T} :
  [.su x :: σ] t = [.su x :: I][^σ] t
:= by
rw[Subst.apply_compose_commute]; simp;

@[simp]
abbrev hs_idx_subst (σ : Subst HsTerm) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .term => λ (t, A) => ([σ]t, [σ]A)
  | .kind => λ (t, A) => ([σ]t, [σ]A)
  | .type => λ (t, A) => ([σ]t, [σ]A)
  | .ctx => λ () => ()

@[simp]
abbrev hs_idx_subst_ty (σ : Subst HsTerm) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .term => λ (t, A) => (t, [σ]A)
  | .kind => λ (t, A) => (t, [σ]A)
  | .type => λ (t, A) => (t, [σ]A)
  | .ctx => λ () => ()



def hs_subst : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm}-> (v: HsVariant) -> {idx : HsJudgmentArgs v} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢τ t : ([σ]T)) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢t t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  HsJudgment v Δ (hs_idx_subst σ idx)
| Γ, Δ, σ, .ctx, (), f1, f2, f3, f4, j, wf => wf
| Γ, Δ, σ, .kind, (t, τ), f1, f2, f3, f4, j, wf => match j with
  | .ax wf' => by constructor; assumption
  | @HsJudgment.arrowk Γ A B h1 h2 => by
    simp;
    have lem1 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h1 wf; simp at lem1
    have lem2 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h2 wf; simp at lem2
    constructor; assumption; assumption;

| Γ, Δ, σ, .type, (t, τ), f1, f2, f3, f4, j, wf => match j with
  | @HsJudgment.varTy Γ x T h1 h2 h3 h4 => by
    generalize zdef : σ x = z at *;
    cases z <;> simp
    case _ y =>
      have lem1 := f1 x y zdef
      have lem2 := f2 x
      have lem3 := @hs_subst Γ Δ σ .kind (T, `□) f1 f2 f3 f4 h4 wf
      rw[zdef]; simp;
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
      have lem := f2 x a T zdef h3
      rw[zdef]; simp;
      apply lem

  | .appk h1 h2 h3 h4 => by
     have lem1 := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
     have lem2 := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h2 wf
     have lem3 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h3 wf
     have lem4 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h4 wf
     apply HsJudgment.appk;
     assumption; assumption; assumption; assumption

  | @HsJudgment.farrow Γ A B h1 h2 h3 => by
    have lem1 := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
    have lem2 : HsValidHeadVariable ([σ]A) Δ.is_opent := by
      apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent
      case _ =>
        intro n t;
        have t' := Frame.is_opent_implies_is_stable t
        have f4' := f4 n t'
        cases f4'; case _ w f3 =>
        exists w; constructor; assumption
        have f1' := f1 n w f3; simp at t;
        replace t := opent_indexing_exists t;
        cases t; case _ t =>
        rw[t] at f1'; simp; rw[<-f1'];
        unfold Frame.apply; unfold Frame.is_opent; simp
      apply h2
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have f1' := hs_lift_subst_rename .empty f1
    have f2' := hs_lift_subst_replace_type .empty wf' f2
    have f3' := hs_lift_subst_replace_term .empty wf' f3
    have f4' := hs_lift_subst_stable .empty f4
    have lem3 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply @hs_subst (.empty :: Γ) (.empty :: Δ) (^σ) .type _ f1' f2' f3' f4' h3 wf'
    apply HsJudgment.farrow;
    apply lem1
    apply lem2
    apply lem3

  | @HsJudgment.allt Γ A B h1 h2 => by
    have lem1 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h1 wf
    have wf' : ⊢s (Frame.kind ([σ]A) :: Δ) := by
      constructor; assumption; assumption
    have f1' := hs_lift_subst_rename (.kind A) f1
    have f2' := hs_lift_subst_replace_type (.kind A) wf' f2
    have f3' := hs_lift_subst_replace_term (.kind A) wf' f3
    have f4' := hs_lift_subst_stable (.kind A) f4
    have lem2 : (Frame.kind ([σ]A) :: Δ) ⊢τ ([^σ]B) : `★ := by
      apply hs_subst .type f1' f2' f3' f4' h2 wf'
    constructor; assumption; assumption

  | @HsJudgment.arrow Γ A B h1 h2 => by
    have lem1 := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have f1' := hs_lift_subst_rename .empty f1
    have f2' := hs_lift_subst_replace_type .empty wf' f2
    have f3' := hs_lift_subst_replace_term .empty wf' f3
    have f4' := hs_lift_subst_stable .empty f4
    have lem2 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply hs_subst .type  f1' f2' f3' f4' h2 wf'
    apply HsJudgment.arrow;
    apply lem1
    apply lem2

| Γ, Δ, σ, .term, (t, τ), f1, f2, f3, f4, j, wf => match j with
  | @HsJudgment.implicitAllI Γ A t τ h1 h2 => by
    simp
    have lem2 := @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h2 wf
    have wf' : ⊢s (.kind ([σ]A) :: Δ) := by
      constructor; assumption; assumption
    have f1' := hs_lift_subst_rename (.kind A) f1
    have f2' := hs_lift_subst_replace_type (.kind A) wf' f2
    have f3' := hs_lift_subst_replace_term (.kind A) wf' f3
    have f4' := hs_lift_subst_stable (.kind A) f4
    have lem := @hs_subst (.kind A :: Γ) (.kind ([σ]A) :: Δ) (^σ) .term _ f1' f2' f3' f4' h1 wf'; simp at lem
    apply HsJudgment.implicitAllI
    rw[Subst.apply_compose_commute]; apply lem
    assumption

  | @HsJudgment.implicitArrI Γ π τ t h1 h2 h3 h4 => by
    simp;
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have lem1 : Δ ⊢τ ([σ]π) : `★ := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
    have f1' := hs_lift_subst_rename .empty f1
    have f2' := hs_lift_subst_replace_type .empty wf' f2
    have f3' := hs_lift_subst_replace_term .empty wf' f3
    have f4' := hs_lift_subst_stable .empty f4
    have lem2 : (.empty :: Δ) ⊢τ ([^σ]τ) : `★ := by
      apply @hs_subst (.empty :: Γ) (.empty :: Δ) (^σ) .type _ f1' f2' f3' f4' h2 wf'
    have wf'' : ⊢s (.type ([σ]π) :: Δ) := by
      constructor; assumption; assumption
    have f1'' := hs_lift_subst_rename (.type π) f1
    have f2'' := hs_lift_subst_replace_type (.type π) wf'' f2
    have f3'' := hs_lift_subst_replace_term (.type π) wf'' f3
    have f4'' := hs_lift_subst_stable (.type π) f4
    have lem3 : (.type ([σ]π) :: Δ) ⊢t ([^σ][S]t) : ([^σ]τ) := by
      apply @hs_subst (.type π :: Γ) (.type ([σ]π) :: Δ) (^σ) .term _ f1'' f2'' f3'' f4'' h4 wf''
    apply HsJudgment.implicitArrI
    assumption
    rw[Subst.lift_unfold] at lem2; assumption
    { apply hs_valid_head_variable_subst Γ.is_opent _
      case _ =>
        intro n t;
        have t' := Frame.is_opent_implies_is_stable t;
        replace f4 := f4 n t'; cases f4;
        case _ w f4 =>
        exists w; apply And.intro; assumption
        have f1' := f1 n w f4; simp; rw[<-f1'];
        simp at t; replace t := opent_indexing_exists t;
        cases t; case _ t =>
          rw[t]; unfold Frame.apply; unfold Frame.is_opent; simp
      case _ => apply h3
    }
    simp at lem3; simp; assumption


  | @HsJudgment.implicitAllE Γ A τ t e τ' h1 h2 h3 h4 h5 => by
    apply HsJudgment.implicitAllE
    apply @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
    apply @hs_subst Γ Δ σ .kind _ f1 f2 f3 f4 h2 wf
    apply @hs_subst Γ Δ σ .term _ f1 f2 f3 f4 h3 wf
    apply @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h4 wf
    rw[h5]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl

  | @HsJudgment.implicitArrE Γ t π τ e τ' h1 h2 h3 h4 => by
    apply HsJudgment.implicitArrE
    apply @hs_subst Γ Δ σ .term _ f1 f2 f3 f4 h1 wf
    apply @hs_subst Γ Δ σ .term _ f1 f2 f3 f4 h2 wf
    rw[h3]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl
    apply @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h4 wf

  | @HsJudgment.var Γ x T h1 h2 h3 => by
    generalize zdef : σ x = z at *;
    cases z <;> (simp; rw[zdef]; simp)
    case _ n =>
      have f1' := f1 x n zdef
      apply HsJudgment.var;
      apply wf
      simp at h2; cases h2;
      case _ h =>
        cases h;
        case _ h =>
          have u := ctor_indexing_exists h;
          cases u; case _ u =>
            rw[<-f1]; rw[u]; unfold Frame.apply; simp; unfold Frame.is_ctor; simp;
            apply zdef
        case _ h =>
          have u := term_indexing_exists h;
          cases u; case _ A u =>
          cases u; case _ t1 u =>
            rw[<-f1]; rw[u]; unfold Frame.apply; simp; unfold Frame.is_term; simp;
            apply zdef
      case _ h =>
        have u := type_indexing_exists h;
        cases u; case _ u =>
          rw[<-f1]; rw[u]; unfold Frame.apply; simp; unfold Frame.is_type; simp;
          apply zdef
      case _ =>
        rw[<-f1']; rw[Frame.get_type_apply_commute]; rw[<-h3]; simp
    case _ a =>
      apply f3 x a T zdef h3


  | @HsJudgment.lam Γ A t B h1 h2 h3 => by

    have lem1 := @hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf
    have wf'' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have wf' : ⊢s (.type ([σ]A) :: Δ) := by
      constructor; assumption; assumption

    have f1' := hs_lift_subst_rename (.type A) f1
    have f2' := hs_lift_subst_replace_type (.type A) wf' f2
    have f3' := hs_lift_subst_replace_term (.type A) wf' f3
    have f4' := hs_lift_subst_stable (.type A) f4

    have f1'' := hs_lift_subst_rename (.empty) f1
    have f2'' := hs_lift_subst_replace_type .empty wf'' f2
    have f3'' := hs_lift_subst_replace_term .empty wf'' f3
    have f4'' := hs_lift_subst_stable .empty f4

    apply HsJudgment.lam
    assumption
    apply @hs_subst (.type A :: Γ) (.type ([σ]A) :: Δ) (^σ) .term _ f1' f2' f3' f4' h2 wf'
    apply @hs_subst (.empty :: Γ) (.empty :: Δ) (^σ) .type _ f1'' f2'' f3'' f4'' h3 wf''


  | @HsJudgment.app Γ t1 A B t2 B' h1 h2 h3 h4 h5 => by
    apply HsJudgment.app
    apply (@hs_subst Γ Δ σ .term _ f1 f2 f3 f4 h1 wf)
    apply (@hs_subst Γ Δ σ .term _ f1 f2 f3 f4 h2 wf)

    rw[h3]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl
    apply (@hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h4 wf)
    apply (@hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h5 wf)


  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
    apply HsJudgment.hsIte
    apply (@hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h1 wf)
    apply (@hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h2 wf)
    apply (@hs_subst Γ Δ σ .type _ f1 f2 f3 f4 h3 wf)
    apply (hs_subst .type f1 f2 f3 f4 h4 wf)
    apply (hs_subst .term f1 f2 f3 f4 h5 wf)
    apply (hs_subst .term f1 f2 f3 f4 h6 wf)
    apply (hs_subst .term f1 f2 f3 f4 h7 wf)
    apply (hs_subst .term f1 f2 f3 f4 h8 wf)
    apply hs_stable_type_match_subst f1 f4 h9
    apply hs_prefix_type_match_subst f1 f4 h10
    apply hs_valid_head_variable_subst Γ.is_datatype _
    case _ =>
      intro n t;
      have t' := Frame.is_datatype_implies_is_stable t;
      replace f4 := f4 n t'; cases f4;
      case _ w f4 =>
      exists w; apply And.intro; assumption
      have f1' := f1 n w f4; simp; rw[<-f1'];
      simp at t; replace t := datatype_indexing_exists t;
      cases t; case _ t =>
        rw[t]; unfold Frame.apply; unfold Frame.is_datatype; simp
    case _ => apply h11;
    apply hs_valid_head_variable_subst Γ.is_ctor _
    case _ =>
      intro n t;
      have t' := Frame.is_ctor_implies_is_stable t;
      replace f4 := f4 n t'; cases f4;
      case _ w f4 =>
      exists w; apply And.intro; assumption
      have f1' := f1 n w f4; simp; rw[<-f1'];
      simp at t; replace t := ctor_indexing_exists t;
      cases t; case _ t =>
        rw[t]; unfold Frame.apply; unfold Frame.is_ctor; simp
    case _ => apply h12

  | @HsJudgment.hslet Γ A t1 B' B t2 h1 h2 h3 h4 h5 => by
    have wf' : ⊢s (.term ([σ]A) ([σ]t1) :: Δ) := by
      apply HsJudgment.wfterm;
      apply hs_subst .type f1 f2 f3 f4 h1 wf
      apply hs_subst .term f1 f2 f3 f4 h2 wf
      apply wf

    have f1' := hs_lift_subst_rename (.term A t1) f1
    have f2' := hs_lift_subst_replace_type (.term A t1) wf' f2
    have f3' := hs_lift_subst_replace_term (.term A t1) wf' f3
    have f4' := hs_lift_subst_stable (.term A t1) f4

    apply HsJudgment.hslet;
    apply hs_subst .type f1 f2 f3 f4 h1 wf
    apply hs_subst .term f1 f2 f3 f4 h2 wf
    rfl
    case _ =>
      have e : [S][σ]B = [^σ][S]B := by
        rw[Subst.apply_compose_commute]; simp
      rw[e]; rw[h3] at h4;
      have h : (.term ([σ]A) ([σ]t1) :: Δ) ⊢t ([^σ]t2) : ([^σ][S] B) := by
        apply @hs_subst (.term A t1 :: Γ) (.term ([σ]A) ([σ]t1) :: Δ) ^σ .term _ f1' f2' f3' f4' h4 wf'
      apply h
    apply hs_subst .type f1 f2 f3 f4 h5 wf
termination_by _ _ _ _ _ _ _ _ _ h => h.size

def hs_beta_empty_type t :
  (.empty::Γ) ⊢τ τ : k ->
  Γ ⊢τ (τ β[t]) : (k β[t])
:= by
intro j
have lem := hs_judgment_ctx_wf .type j;
cases lem; case _ lem =>
apply @hs_subst (.empty :: Γ) Γ (.su t :: I) .type (τ, k) _ _ _ _ j lem;
case _ =>
  intro n y h;
  cases n <;> simp at *; subst h
  case _ => rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2
case _ =>
  intro n t T h1 h2
  cases n <;> simp at *; subst h1
  injection h2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1


def hs_beta_kind_type :
  (.kind A::Γ) ⊢τ τ : k ->
  Γ ⊢τ t : A ->
  Γ ⊢τ (τ β[t]) : (k β[t])
:= by
intro j1 j2
have lem := hs_judgment_ctx_wf .type j2;
apply @hs_subst (.kind A :: Γ) Γ (.su t :: I) .type (τ, k) _ _ _ _ j1 lem;
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
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e; simp
  sorry
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1




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
