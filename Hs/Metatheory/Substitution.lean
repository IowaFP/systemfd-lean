import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken
import Hs.Metatheory.FrameWf
import Hs.Metatheory.Uniqueness

set_option maxHeartbeats 1000000

@[simp]
abbrev hs_idx_subst_ty (σ : Subst HsTerm) : (HsTerm × HsTerm) -> HsJudgmentArgs v :=
  match v with
  | .term => λ (t, A) => (t, [σ]A)
  | .kind => λ (t, A) => (t, [σ]A)
  | .type => λ (t, A) => (t, [σ]A)
  | .ctx => λ _ => ()

def hs_lift_subst_replace (A : Frame HsTerm) :
  ⊢s (A.apply σ :: Δ) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type ->
     HsJudgment v Δ (hs_idx_subst_ty σ (t, T))) ->
  (∀ n t T, ^σ n = .su t -> .some T = ((A::Γ) d@ n).get_type ->
     HsJudgment v (A.apply σ :: Δ) (hs_idx_subst_ty (^σ) (t, T)))
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
    have lem4 := hs_weaken v j h1;
    cases v
    all_goals(simp; simp at lem4)
    all_goals try (unfold S at lem3; unfold Ren.to at lem4; rw [lem3] at lem4; simp at lem4; apply lem4)
    case _ => apply j

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


def hs_subst_kind : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm}  ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  Γ ⊢κ t : k ->
  ⊢s Δ ->
  Δ ⊢κ ([σ]t) : ([σ]k)
| Γ, Δ, σ, f1, f3, j, wf => match j with
  | .ax wf' => by constructor; assumption
  | @HsJudgment.arrowk Γ A B h1 h2 => by
    have lem1 := hs_subst_kind f1 f3 h1 wf; simp at lem1
    have lem2 := hs_subst_kind f1 f3 h2 wf; simp at lem2
    constructor; assumption; assumption;

def hs_subst_type : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type ->  Δ ⊢τ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  Γ ⊢τ t : τ ->
  ⊢s Δ ->
  Δ ⊢τ ([σ]t) : ([σ]τ)

| Γ, Δ, σ, f1, f2, f3, j, wf => match j with
  | @HsJudgment.varTy Γ x T h1 h2 h3 h4 => by
    generalize zdef : σ x = z at *;
    cases z <;> simp
    case _ y =>
      have lem1 := f1 x y zdef
      have lem2 := f2 x
      have lem3 := hs_subst_kind f1 f3 h4 wf
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
      rw[zdef]; simp;
      have lem := f2 x a T zdef h3;
      simp at lem;
      apply lem

  | .appk h1 h2 h3 h4 => by
     have lem1 := hs_subst_type f1 f2 f3 h1 wf
     have lem2 := hs_subst_type f1 f2 f3 h2 wf
     have lem3 := hs_subst_kind f1 f3 h3 wf
     have lem4 := hs_subst_kind f1 f3 h4 wf
     apply HsJudgment.appk;
     assumption; assumption; assumption; assumption

  | @HsJudgment.farrow Γ A B h1 h2 h3 => by
    have lem1 := hs_subst_type f1 f2 f3 h1 wf
    have lem2 : HsValidHeadVariable ([σ]A) Δ.is_opent := by
      apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent
      case _ =>
        intro n t;
        have t' := Frame.is_opent_implies_is_stable t
        have f3' := f3 n t'
        cases f3'; case _ w f3 =>
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
    have f2' := hs_lift_subst_replace .empty wf' f2
    have f3' := hs_lift_subst_stable .empty f3
    have lem3 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply @hs_subst_type _ _ (.empty :: Γ) (.empty :: Δ) (^σ) f1' f2' f3' h3 wf'
    apply HsJudgment.farrow;
    apply lem1
    apply lem2
    apply lem3

  | @HsJudgment.allt Γ A B h1 h2 => by
    have lem1 := hs_subst_kind f1 f3 h1 wf
    have wf' : ⊢s (Frame.kind ([σ]A) :: Δ) := by
      constructor; assumption; assumption
    have f1' := hs_lift_subst_rename (.kind A) f1
    have f2' := hs_lift_subst_replace (.kind A) wf' f2
    have f3' := hs_lift_subst_stable (.kind A) f3
    have lem2 : (Frame.kind ([σ]A) :: Δ) ⊢τ ([^σ]B) : `★ := by
      apply hs_subst_type f1' f2' f3' h2 wf'
    constructor; assumption; assumption

  | @HsJudgment.arrow Γ A B h1 h2 => by
    have lem1 := hs_subst_type f1 f2 f3 h1 wf
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have f1' := hs_lift_subst_rename .empty f1
    have f2' := hs_lift_subst_replace .empty wf' f2
    have f3' := hs_lift_subst_stable .empty f3
    have lem2 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
      apply hs_subst_type f1' f2' f3' h2 wf'
    apply HsJudgment.arrow;
    apply lem1
    apply lem2

def hs_subst_term : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢τ t : ([σ]T)) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢t t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  Γ ⊢t t : T ->
  ⊢s Δ ->
  Δ ⊢t ([σ]t) : ([σ]T)
| Γ, Δ, σ, f1, f2, f3, f4, j, wf => match j with
  | @HsJudgment.implicitAllI Γ A t τ h1 h2 => by
    simp
    have lem2 := hs_subst_kind f1 f4 h2 wf
    have wf' : ⊢s (.kind ([σ]A) :: Δ) := by
      constructor; assumption; assumption
    have f1' := hs_lift_subst_rename (.kind A) f1
    have f2' := hs_lift_subst_replace (.kind A) wf' f2
    have f3' := hs_lift_subst_replace (.kind A) wf' f3
    have f4' := hs_lift_subst_stable (.kind A) f4
    have lem := @hs_subst_term _ _ (.kind A :: Γ) (.kind ([σ]A) :: Δ) (^σ) f1' f2' f3' f4' h1 wf'; simp at lem
    apply HsJudgment.implicitAllI
    rw[Subst.apply_compose_commute]; apply lem
    assumption

  | @HsJudgment.implicitArrI Γ π τ t h1 h2 h3 h4 => by
    simp;
    have wf' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have lem1 : Δ ⊢τ ([σ]π) : `★ := hs_subst_type f1 f2 f4 h1 wf
    have f1' := hs_lift_subst_rename .empty f1
    have f2' := hs_lift_subst_replace .empty wf' f2
    have f3' := hs_lift_subst_replace .empty wf' f3
    have f4' := hs_lift_subst_stable .empty f4
    have lem2 : (.empty :: Δ) ⊢τ ([^σ]τ) : `★ := by
      apply @hs_subst_type _ _ (.empty :: Γ) (.empty :: Δ) (^σ) f1' f2' f4' h2 wf'
    have wf'' : ⊢s (.type ([σ]π) :: Δ) := by
      constructor; assumption; assumption
    have f1'' := hs_lift_subst_rename (.type π) f1
    have f2'' := hs_lift_subst_replace (.type π) wf'' f2
    have f3'' := hs_lift_subst_replace (.type π) wf'' f3
    have f4'' := hs_lift_subst_stable (.type π) f4
    have lem3 : (.type ([σ]π) :: Δ) ⊢t ([^σ][S]t) : ([^σ]τ) := by
      apply @hs_subst_term _ _  (.type π :: Γ) (.type ([σ]π) :: Δ) (^σ) f1'' f2'' f3'' f4'' h4 wf''
    apply HsJudgment.implicitArrI
    assumption
    rw[Subst.lift_unfold] at lem2; assumption
    { apply hs_valid_head_variable_subst Γ.is_opent _
      case _ =>
        intro n t;
        have t' := Frame.is_opent_implies_is_stable t;
        replace f4 := f4 n t'; cases f4;
        case _ w f3 =>
        exists w; apply And.intro; assumption
        have f1' := f1 n w f3; simp; rw[<-f1'];
        simp at t; replace t := opent_indexing_exists t;
        cases t; case _ t =>
          rw[t]; unfold Frame.apply; unfold Frame.is_opent; simp
      case _ => apply h3
    }
    simp at lem3; simp; assumption

  | @HsJudgment.implicitAllE Γ A τ t e τ' h1 h2 h3 h4 h5 => by
    apply HsJudgment.implicitAllE
    apply hs_subst_type f1 f2 f4 h1 wf
    apply hs_subst_kind f1 f4 h2 wf
    apply hs_subst_term f1 f2 f3 f4 h3 wf
    apply hs_subst_type f1 f2 f4 h4 wf
    rw[h5]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl

  | @HsJudgment.implicitArrE Γ t π τ e τ' h1 h2 h3 h4 => by
    apply HsJudgment.implicitArrE
    apply hs_subst_term f1 f2 f3 f4 h1 wf
    apply hs_subst_term f1 f2 f3 f4 h2 wf
    rw[h3]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl
    apply hs_subst_type f1 f2 f4 h4 wf

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

    have lem1 := hs_subst_type f1 f2 f4 h1 wf
    have wf'' : ⊢s (.empty :: Δ) := by
      constructor; assumption
    have wf' : ⊢s (.type ([σ]A) :: Δ) := by
      constructor; assumption; assumption

    have f1' := hs_lift_subst_rename (.type A) f1
    have f2' := hs_lift_subst_replace (.type A) wf' f2
    have f3' := hs_lift_subst_replace (.type A) wf' f3
    have f4' := hs_lift_subst_stable (.type A) f4

    have f1'' := hs_lift_subst_rename .empty f1
    have f2'' := hs_lift_subst_replace .empty wf'' f2
    have f3'' := hs_lift_subst_replace .empty wf'' f3
    have f4'' := hs_lift_subst_stable .empty f4

    apply HsJudgment.lam
    assumption
    apply @hs_subst_term _ _ (.type A :: Γ) (.type ([σ]A) :: Δ) (^σ) f1' f2' f3' f4' h2 wf'
    apply @hs_subst_type _ _ (.empty :: Γ) (.empty :: Δ) (^σ) f1'' f2'' f4'' h3 wf''

  | @HsJudgment.app Γ t1 A B t2 B' h1 h2 h3 h4 h5 => by
    apply HsJudgment.app
    apply hs_subst_term f1 f2 f3 f4 h1 wf
    apply hs_subst_term f1 f2 f3 f4 h2 wf

    rw[h3]; rw[Subst.apply_compose_commute]; simp; rw[<-Subst.lift_unfold]; rw[subst_valid]; rfl
    apply (hs_subst_type f1 f2 f4 h4 wf)
    apply (hs_subst_type f1 f2 f4 h5 wf)

  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
    apply HsJudgment.hsIte
    apply (hs_subst_type f1 f2 f4 h1 wf)
    apply (hs_subst_type f1 f2 f4 h2 wf)
    apply (hs_subst_type f1 f2 f4 h3 wf)
    apply (hs_subst_type f1 f2 f4 h4 wf)
    apply (hs_subst_term f1 f2 f3 f4 h5 wf)
    apply (hs_subst_term f1 f2 f3 f4 h6 wf)
    apply (hs_subst_term f1 f2 f3 f4 h7 wf)
    apply (hs_subst_term f1 f2 f3 f4 h8 wf)
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
      apply hs_subst_type f1 f2 f4 h1 wf
      apply hs_subst_term f1 f2 f3 f4 h2 wf
      apply wf

    have f1' := hs_lift_subst_rename (.term A t1) f1
    have f2' := hs_lift_subst_replace (.term A t1) wf' f2
    have f3' := hs_lift_subst_replace (.term A t1) wf' f3
    have f4' := hs_lift_subst_stable (.term A t1) f4

    apply HsJudgment.hslet;
    apply hs_subst_type f1 f2 f4 h1 wf
    apply hs_subst_term f1 f2 f3 f4 h2 wf
    rfl
    case _ =>
      have e : [S][σ]B = [^σ][S]B := by
        rw[Subst.apply_compose_commute]; simp
      rw[e]; rw[h3] at h4;
      have h : (.term ([σ]A) ([σ]t1) :: Δ) ⊢t ([^σ]t2) : ([^σ][S] B) := by
        apply @hs_subst_term _ _ (.term A t1 :: Γ) (.term ([σ]A) ([σ]t1) :: Δ) ^σ f1' f2' f3' f4' h4 wf'
      apply h
    apply hs_subst_type f1 f2 f4 h5 wf
termination_by _ _ _ _ _ _ _ h => h.size



def hs_beta_empty_type t :
  (.empty::Γ) ⊢τ τ : k ->
  Γ ⊢τ (τ β[t]) : (k β[t])
:= by
intro j
have wf := hs_judgment_ctx_wf .type j;
cases wf; case _ wf =>
apply @hs_subst_type τ k (.empty :: Γ) Γ (.su t :: I) _ _ _ j wf;
case _ =>
  intro n y h;
  cases n <;> simp at *; subst h
  case _ => rw [Frame.apply_compose]; simp
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


def hs_beta_kind_type :
  (.kind A::Γ) ⊢τ τ : k ->
  Γ ⊢τ t : A ->
  Γ ⊢τ (τ β[t]) : (k β[t])
:= by
intro j1 j2;
have wf := hs_judgment_ctx_wf .type j1;
cases wf; case _ wf _ =>
apply @hs_subst_type τ k (.kind A :: Γ) Γ (.su t :: I) _ _ _ j1 wf;
case _ =>
  intro n y h1
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  injection h2 with e; subst e;
  simp; assumption
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1


def hs_replace_empty_kind_lemma : (τ k : HsTerm) -> (Γ Γ' : Ctx HsTerm) ->
  (Γ d@ n) = .empty ->
  Γ.drop (n + 1) ⊢s f ->
  Γ.modify n (λ _ => f) = Γ' ->
  ⊢s Γ' ->
  Γ ⊢κ τ : k ->
  Γ' ⊢κ τ : k := by
intro τ k Γ Γ' j1 j2 j3 j4 j5;
cases j5;
case _ =>
  constructor; assumption
case _ A B h1 h2 =>
  constructor;
  apply hs_replace_empty_kind_lemma A `□ Γ Γ' j1 j2 j3 j4 h1
  apply hs_replace_empty_kind_lemma B `□ Γ Γ' j1 j2 j3 j4 h2
termination_by h => h.size

def hs_replace_empty_kind : (k : HsTerm) ->
  (.empty :: Γ) ⊢κ k : s ->
  Γ ⊢s f ->
  (f :: Γ) ⊢κ k : s := by
intro k j1 j2
have lem : (.empty :: Γ) d@ 0 = .empty := by simp; unfold Frame.apply; simp
apply hs_replace_empty_kind_lemma k s (.empty :: Γ) (f :: Γ);
assumption
simp; assumption
simp; apply Ctx.hs_weaken_frame; apply hs_frame_wf_implies_wf; assumption
assumption
assumption

theorem n_x_different : (Γ : Ctx HsTerm) ->
  Γ d@ n = .empty ->
  (Γ d@ x).get_type = .some k ->
  x ≠ n := by
intro Γ j1 j2 j3;
rw[j3] at j2; rw[j1] at j2; unfold Frame.get_type at j2; simp at j2;

def hs_replace_type_lemma : (τ k : HsTerm) -> (Γ Γ' : Ctx HsTerm) ->
  (Γ d@ n) = .empty ->
  Γ.drop (n + 1) ⊢s f ->
  Γ.modify n (λ _ => f) = Γ' ->
  ⊢s Γ' ->
  Γ ⊢τ τ : k ->
  Γ' ⊢τ τ : k := by
intro τ k Γ Γ' j1 j2 j3 j4 j5;
have lem : ∀ f, (f :: Γ) d@ (n + 1) = .empty := by intro f; simp; unfold Frame.apply; rw[j1]
cases j5;
case _ A B h1 h2 =>
  constructor;
  apply hs_replace_empty_kind_lemma A `□ Γ Γ' j1 j2 j3 j4 h1
  apply hs_replace_type_lemma B `★ (.kind A :: Γ) (.kind A :: Γ');
  apply lem
  assumption
  simp; assumption
  constructor;
  apply hs_replace_empty_kind_lemma A `□ Γ Γ' j1 j2 j3 j4 h1
  assumption
  assumption
case _ A B h1 h2 =>
  constructor
  apply hs_replace_type_lemma A `★ Γ Γ' j1 j2 j3 j4 h1
  apply hs_replace_type_lemma B `★ (.empty :: Γ) (.empty :: Γ');
  apply lem
  assumption
  simp; assumption
  constructor; assumption
  assumption
case _ A B h1 h2 h3 =>
  constructor
  apply hs_replace_type_lemma A `★ Γ Γ' j1 j2 j3 j4 h1
  apply hs_replace_empty_valid_head_variable_opent Γ Γ' j1 j3 h2
  apply hs_replace_type_lemma B `★ (.empty :: Γ) (.empty :: Γ');
  apply lem
  assumption
  simp; assumption
  constructor; assumption
  assumption
case _ f A a h1 h2 h3 h4 =>
  constructor;
  apply hs_replace_type_lemma f (A `-k> k) Γ Γ' j1 j2 j3 j4 h3
  apply hs_replace_type_lemma a A Γ Γ' j1 j2 j3 j4 h1
  apply hs_replace_empty_kind_lemma A `□ Γ Γ' j1 j2 j3 j4 h2
  apply hs_replace_empty_kind_lemma k `□ Γ Γ' j1 j2 j3 j4 h4
case _ x wf h1 h2 h3 =>
  have lem1 := n_x_different Γ j1 (Eq.symm h2)
  have lem2 := replace_eq_except Γ Γ' j3 x lem1
  constructor;
  assumption
  case _ => rw [<-lem2]; assumption
  case _ => rw [<-lem2]; assumption
  apply hs_replace_empty_kind_lemma k `□ Γ Γ' j1 j2 j3 j4 h3

termination_by h => h.size

-- #eval ([1,2,3]).modify 1 (λ _ => 5)
-- #eval ([1,2,3].take 1 ++ [5] ++ [1,2,3].drop 2)


def hs_replace_empty_type_lemma : (τ : HsTerm) ->
  (.empty :: Γ) ⊢τ τ : k ->
  Γ ⊢s f ->
  (f :: Γ) ⊢τ τ : k := by
intro τ j f;
have lem1 : (.empty :: Γ) d@ 0 = .empty := by simp; unfold Frame.apply; simp
apply hs_replace_type_lemma
assumption
assumption
unfold List.modify; simp
apply Ctx.hs_weaken_frame; apply hs_frame_wf_implies_wf f; assumption
assumption

def hs_replace_empty_type :
  Γ ⊢τ A : `★ ->
  (.empty :: Γ) ⊢τ B : `★ ->
  (.type A :: Γ) ⊢τ B : `★ :=
by
intro j1 j2
have wf := hs_judgment_ctx_wf .type j1
have lem : Γ ⊢s (.type A) := by constructor; assumption
apply hs_replace_empty_type_lemma; assumption; assumption


def hs_subst_type' : (v : HsVariant) -> (v = .type) -> {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm}
  -> {idx : HsJudgmentArgs v} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type ->  Δ ⊢τ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  HsJudgment v Γ idx ->
  ⊢s Δ ->
  HsJudgment v Γ (hs_idx_subst σ idx) := by
intro v ev Γ Δ σ idx f1 f2 f3 j wf
cases j <;> simp at *
all_goals (clear ev)
case _ => sorry
case _ => sorry
case _ => sorry
case _ f A B a h1 h2 h3 h4 =>
 have lem1 := hs_subst_type f1 f2 f3 h1 wf; simp at lem1;
 have lem2 := hs_subst_type f1 f2 f3 h2 wf
 have lem3 := hs_subst_kind f1 f3 h3 wf
 have lem4 := hs_subst_kind f1 f3 h4 wf
 apply HsJudgment.appk;
 sorry
 sorry
 sorry
 sorry
 sorry

case _ => sorry
-- | Γ, Δ, σ, f1, f2, f3, j, wf => match j with
--   | @HsJudgment.varTy Γ x T h1 h2 h3 h4 => by
--     generalize zdef : σ x = z at *;
--     cases z <;> simp
--     case _ y =>
--       have lem1 := f1 x y zdef
--       have lem2 := f2 x
--       have lem3 := hs_subst_kind f1 f3 h4 wf
--       rw[zdef]; simp;
--       apply HsJudgment.varTy;
--       apply wf
--       rw[<-lem1]; simp;
--       simp at h2; cases h2;
--       case _ h =>
--         have u := datatype_indexing_exists h;
--         cases u; case _ u =>
--         apply Or.inl;
--         rw[u]; unfold Frame.apply; simp; unfold Frame.is_datatype; simp
--       case _ h =>
--         have u := kind_indexing_exists h;
--         cases u; case _ u =>
--         apply Or.inr;
--         rw[u]; unfold Frame.apply; simp; unfold Frame.is_kind; simp
--       case _ =>
--         rw[<-lem1]; rw[Frame.get_type_apply_commute]; rw[<-h3]; simp;
--       apply lem3
--     case _ a =>
--       rw[zdef]; simp;
--       have lem := f2 x a T zdef h3;
--       simp at lem;
--       apply lem

--   | .appk h1 h2 h3 h4 => by
--      have lem1 := hs_subst_type f1 f2 f3 h1 wf
--      have lem2 := hs_subst_type f1 f2 f3 h2 wf
--      have lem3 := hs_subst_kind f1 f3 h3 wf
--      have lem4 := hs_subst_kind f1 f3 h4 wf
--      apply HsJudgment.appk;
--      assumption; assumption; assumption; assumption

--   | @HsJudgment.farrow Γ A B h1 h2 h3 => by
--     have lem1 := hs_subst_type f1 f2 f3 h1 wf
--     have lem2 : HsValidHeadVariable ([σ]A) Δ.is_opent := by
--       apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent
--       case _ =>
--         intro n t;
--         have t' := Frame.is_opent_implies_is_stable t
--         have f3' := f3 n t'
--         cases f3'; case _ w f3 =>
--         exists w; constructor; assumption
--         have f1' := f1 n w f3; simp at t;
--         replace t := opent_indexing_exists t;
--         cases t; case _ t =>
--         rw[t] at f1'; simp; rw[<-f1'];
--         unfold Frame.apply; unfold Frame.is_opent; simp
--       apply h2
--     have wf' : ⊢s (.empty :: Δ) := by
--       constructor; assumption
--     have f1' := hs_lift_subst_rename .empty f1
--     have f2' := hs_lift_subst_replace .empty wf' f2
--     have f3' := hs_lift_subst_stable .empty f3
--     have lem3 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
--       apply @hs_subst_type _ _ (.empty :: Γ) (.empty :: Δ) (^σ) f1' f2' f3' h3 wf'
--     apply HsJudgment.farrow;
--     apply lem1
--     apply lem2
--     apply lem3

--   | @HsJudgment.allt Γ A B h1 h2 => by
--     have lem1 := hs_subst_kind f1 f3 h1 wf
--     have wf' : ⊢s (Frame.kind ([σ]A) :: Δ) := by
--       constructor; assumption; assumption
--     have f1' := hs_lift_subst_rename (.kind A) f1
--     have f2' := hs_lift_subst_replace (.kind A) wf' f2
--     have f3' := hs_lift_subst_stable (.kind A) f3
--     have lem2 : (Frame.kind ([σ]A) :: Δ) ⊢τ ([^σ]B) : `★ := by
--       apply hs_subst_type f1' f2' f3' h2 wf'
--     constructor; assumption; assumption

--   | @HsJudgment.arrow Γ A B h1 h2 => by
--     have lem1 := hs_subst_type f1 f2 f3 h1 wf
--     have wf' : ⊢s (.empty :: Δ) := by
--       constructor; assumption
--     have f1' := hs_lift_subst_rename .empty f1
--     have f2' := hs_lift_subst_replace .empty wf' f2
--     have f3' := hs_lift_subst_stable .empty f3
--     have lem2 : (Frame.empty :: Δ) ⊢τ ([^σ] B) : `★ := by
--       apply hs_subst_type f1' f2' f3' h2 wf'
--     apply HsJudgment.arrow;
--     apply lem1
--     apply lem2
