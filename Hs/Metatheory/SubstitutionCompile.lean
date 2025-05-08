import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.UniquenessCompile
import Hs.Algorithm

set_option maxHeartbeats 1000000

def subst_compile_kind : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm} -> {σ' : Subst Term} ->
  (j : Γ ⊢κ t : k) ->
  compile_kind Γ t k j = .some t' ->
  ⊢s Δ ->

  (sj : Δ ⊢κ ([σ]t) : ([σ]k)) ->
  compile_kind Δ ([σ]t) ([σ]k) sj = .some ([σ']t') := by
intro Γ Δ σ σ' j cj wf sj
induction Γ, t, k, j using compile_kind.induct generalizing Δ t'
case _ Γ j =>
  unfold compile_kind; cases sj; simp;
  unfold compile_kind at cj; cases cj; simp;
case _ Γ A B j1 j2 ih1 ih2 =>
  unfold compile_kind at cj; simp at cj;
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  cases cj
  cases sj; case _ jA' jB' =>
  unfold compile_kind; simp;
  rw[Option.bind_eq_some];
  exists ([σ']A');
  constructor;
  apply @ih1 A' Δ cA wf jA'
  rw[Option.bind_eq_some];
  exists ([σ']B')
  constructor;
  apply @ih2 B' Δ cB wf jB'
  simp


theorem lifting_substitution_compile : (σ : Subst HsTerm) -> (σ' : Subst Term) ->
  (∀ (n y : Nat), σ n = .re y -> σ' n = .re y) ->
  (∀ (n y y' : Nat), σ n = .re y -> (^σ) n = .re y' -> (^σ') n = .re y') := by
intro σ σ' f n y y' h1 h2 <;> simp at *
have f := f n y h1
cases n <;> simp at *;
case _ => assumption
case _ n =>
  unfold Subst.compose at *; simp at *

  sorry


def subst_compile_type : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm} -> {σ' : Subst Term} ->
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (f1 : ∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->

  (f2 : ∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢τ t : ([σ]T)) ->

  (f3 : ∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->

  -- Substitutions are related via compilation
  (∀ n y, σ n = .re y -> σ' n = .re y) ->
  (∀ n t, σ n = .su t -> ∃ t', σ' n = .su t') ->
  (∀ i t T wt,
     σ i = .su t ->
     σ' i = .su wt ->
     (j : Δ ⊢τ t : T) ->
     compile_type Δ t T j = .some wt
  ) ->

  (j : Γ ⊢τ t : k) ->
  compile_type Γ t k j = .some t' ->
  ⊢s Δ ->

  (sj : Δ ⊢τ ([σ]t) :  ([σ] k)) ->

  compile_type Δ ([σ]t) ([σ]k) sj = .some ([σ']t')
:= by
intro Γ Δ σ σ' h f1 f2 f3 f4 f5 f6 j cj wf sj
induction Γ, t, k, j using compile_type.induct generalizing Δ t' σ σ'
case _ Γ T n wf' test gt ck  =>
  have j := HsJudgment.varTy wf' test gt ck
  generalize jh1 : HsJudgment.varTy wf' test gt ck = j' at *;
  have u := types_have_unique_judgments h j j'; cases u
  generalize zdef : σ n = y at *;
  cases y;
  case _ x =>
    unfold compile_type at cj; simp at cj; rw[<-jh1] at cj;
    rw[Option.bind_eq_some] at cj;
    cases cj; case _ T' cj =>
    cases cj; case _ cT cj =>
    cases cj;
    simp at sj; rw[zdef] at sj; simp at sj;
    simp
    have lem4 := f4 n x zdef; rw[lem4]; simp;
    have lem5 : compile_type Δ (`#x) ([σ]T) sj = .some #x := by
      unfold compile_type; cases sj; case _ jk _ =>
      simp; rw[Option.bind_eq_some]
      exists ([σ']T')
      constructor;
      have u := @subst_compile_kind T `□ T' Γ Δ σ σ' ck cT wf jk;
      rw[<-u]; congr;
      rfl
    rw[<-lem5];
    apply compile_type_congr;
    apply h
    simp; rw[zdef]
    rfl
  case _ t =>
    have cj' := cj
    unfold compile_type at cj'; simp at cj'; rw[<-jh1] at cj';
    rw[Option.bind_eq_some] at cj';
    cases cj'; case _ T' cj' =>
    cases cj'; case _ cT cj' =>
    cases cj';
    have f5 := f5 n t zdef; cases f5; case _ wt f5 =>
    have lem2 := f2 n t T zdef gt
    have f6 := f6 n t ([σ]T) wt zdef f5 lem2
    simp; rw[f5]; simp; rw[<-f6]
    apply compile_type_congr h
    simp; rw[zdef]
    rfl

case _ Γ B f A a jf ja jA jB ih1 ih2 => -- appk
  generalize ej : hs_subst_type f1 f2 f3 (jf.appk ja jA jB) wf = sj' at *;
  have u := types_have_unique_judgments h sj sj'; cases u;
  unfold compile_type at cj; simp at cj;
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ f' cj =>
  cases cj; case _ cf cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ a' cj =>
  cases cj; case _ ca cj =>
  cases cj;
  rw[<-ej]
  unfold compile_type; simp; unfold hs_subst_type; simp;
  rw[Option.bind_eq_some]
  exists([σ']A')
  constructor;
  apply subst_compile_kind jA cA wf
  rw[Option.bind_eq_some]
  exists([σ']B')
  constructor;
  apply subst_compile_kind jB cB wf
  rw[Option.bind_eq_some]
  exists([σ']f')
  constructor;
  apply @ih1 f' Δ σ σ' f1 f2 f3 f4 f5 f6 cf wf
  rw[Option.bind_eq_some]
  exists ([σ']a')
  constructor
  simp
  apply @ih2 a' Δ σ σ' f1 f2 f3 f4 f5 f6 ca wf
  simp

case _ Γ A B jA jB ih => -- allt
  have lem : (Option.map (λ x => [σ'] x) (compile_type Γ (`∀{A} B) `★ (jA.allt jB)))
             = (Option.map (λ x => [σ'] x) (.some t')) := by rw [cj]
  have lem' : (Option.map (λ x => [σ'] x) (.some t')) = .some ([σ'] t') := by  simp
  rw[lem'] at lem; rw[<-lem];
  simp
  have lem'' := compile_preserves_type_shape_all (jA.allt jB) cj;
  cases lem''; case _ A' lem'' =>
  cases lem''; case _ B' lem'' =>
  cases lem''
  rw[cj]; simp;
  unfold compile_type at cj; simp at cj;
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  cases cj;
  generalize ej : hs_subst_type f1 f2 f3 (jA.allt jB) wf = sj' at *;
  have u := types_have_unique_judgments h sj sj'; cases u;
  unfold compile_type; simp; unfold hs_subst_type at ej; simp at ej; rw[<-ej]
  rw[Option.bind_eq_some]
  exists ([σ']A')
  constructor;
  apply subst_compile_kind jA cA wf

  rw[Option.bind_eq_some]
  exists ([^σ'] B')
  constructor;

  have lem := hs_subst_kind f1 f3 jA wf; rw[HsTerm.subst_HsKind] at lem;
  have wf'' : ⊢s (.kind ([σ]A) :: Δ) := by apply HsJudgment.wfkind; assumption; assumption
  generalize wfh : (hs_subst_kind f1 f3 jA wf).wfkind wf = wf' at *;
  generalize f1e : hs_lift_subst_rename (.kind A) f1 = f1' at *
  generalize f2e : hs_lift_subst_replace (.kind A) wf'' f2 = f2' at *
  generalize f3e : hs_lift_subst_stable (.kind A) f3 = f3' at *

  apply  @ih B' (.kind ([σ]A) :: Δ) (^σ) (^σ') f1' f2' f3' _ _ _ cB wf'
  case _ =>
    intro n y;
    sorry
  case _ =>
    intro n t h
    cases n <;> simp
    case _ => simp at h
    case _ n =>
      generalize zdef : σ n = y at *;
      cases y <;> (simp at h; unfold Subst.compose at h; simp at h; rw[zdef] at h; simp at h)
      case _ a =>
        have f5 := f5 n a zdef; cases f5; case _ t' f5 =>
        simp at f5;
        exists [S] t';
        unfold Subst.compose; simp; rw[f5]
  case _ =>
    intro n t T wt;
    sorry
  simp;

case _ Γ A B jA jB ih1 ih2 => -- arrow
  have lem : (Option.map (λ x => [σ'] x) (compile_type Γ (A → B) `★ (jA.arrow jB)))
             = (Option.map (λ x => [σ'] x) (.some t')) := by rw [cj]
  have lem' : (Option.map (λ x => [σ'] x) (.some t')) = .some ([σ'] t') := by  simp
  rw[lem'] at lem; rw[<-lem];
  simp
  have lem'' := compile_preserves_type_shape_arrow (jA.arrow jB) cj;
  cases lem''; case _ A' lem'' =>
  cases lem''; case _ B' lem'' =>
  cases lem''; case _ jA' lem'' =>
  cases lem''; case _ jB' lem'' =>
  cases lem''; case _ e lem'' =>
  cases e
  cases lem''; case _ cjA cjB =>
  have u := types_have_unique_judgments h jA jA'; cases u
  have u := types_have_unique_judgments h jB jB'; cases u
  rw[cj]; simp;
  generalize ej : hs_subst_type f1 f2 f3 (jA.arrow jB) wf = sj' at *;
  have u := types_have_unique_judgments h sj sj'; cases u;

  unfold compile_type; simp; rw [<-ej]; unfold hs_subst_type; simp;
  rw[Option.bind_eq_some]
  exists ([σ']A')
  constructor;
  cases sj; case _ sjA sjB =>
    clear ih2;
    unfold hs_subst_type at ej; simp at ej; cases ej;
    apply @ih1 A' Δ σ σ' f1 f2 f3 f4 f5 f6 cjA wf

  rw[Option.bind_eq_some]
  exists ([^σ'] B')
  constructor;
  clear ih1;
  unfold hs_subst_type at ej; simp at ej; cases ej;
  have wf' : ⊢s (.empty :: Δ) := by constructor; assumption
  have f1' := hs_lift_subst_rename .empty f1

  generalize fh : @hs_lift_subst_replace σ Δ Γ .type .empty wf' f2 = f2' at *;
  have ef2 : @hs_lift_subst_replace σ Δ Γ .type .empty wf' f2 = f2' := by
    rw [fh]

  have f3' := hs_lift_subst_stable .empty f3

  apply  @ih2 B' (.empty :: Δ) (^σ) (^σ') f1' f2' f3' _ _ _ cjB wf'
  sorry
  case _ =>
    intro n t h
    cases n <;> simp
    case _ => simp at h
    case _ n =>
      generalize zdef : σ n = y at *;
      cases y <;> (simp at h; unfold Subst.compose at h; simp at h; rw[zdef] at h; simp at h)
      case _ a =>
        have f5 := f5 n a zdef; cases f5; case _ t' f5 =>
        simp at f5;
        exists [S] t';
        unfold Subst.compose; simp; rw[f5]
  sorry
  simp

case _ Γ A B jA vhv jB ih1 ih2 =>  -- farrow
  have lem : (Option.map (λ x => [σ'] x) (compile_type Γ (A ⇒ B) `★ (.farrow jA vhv jB)))
             = (Option.map (λ x => [σ'] x) (.some t')) := by rw [cj]
  have lem' : (Option.map (λ x => [σ'] x) (.some t')) = .some ([σ'] t') := by  simp
  rw[lem'] at lem; rw[<-lem];
  simp
  have lem'' := compile_preserves_type_shape_arrow (jA.arrow jB) cj;
  cases lem''; case _ A' lem'' =>
  cases lem''; case _ B' lem'' =>
  cases lem''; case _ jA' lem'' =>
  cases lem''; case _ jB' lem'' =>
  cases lem''; case _ e lem'' =>
  cases e
  cases lem''; case _ cjA cjB =>
  have u := types_have_unique_judgments h jA jA'; cases u
  have u := types_have_unique_judgments h jB jB'; cases u
  rw[cj]; simp;
  generalize ej : hs_subst_type f1 f2 f3 (jA.farrow vhv jB) wf = sj' at *;
  have u := types_have_unique_judgments h sj sj'; cases u;

  unfold compile_type; simp; rw [<-ej]; unfold hs_subst_type; simp;
  rw[Option.bind_eq_some]
  exists ([σ']A')
  constructor;
  cases sj; case _ sjA sjB =>
    clear ih2;
    unfold hs_subst_type at ej; simp at ej; cases ej;
    apply @ih1 A' Δ σ σ' f1 f2 f3 f4 f5 f6 cjA wf

  rw[Option.bind_eq_some]
  exists ([^σ'] B')
  constructor;
  clear ih1;
  unfold hs_subst_type at ej; simp at ej; cases ej;
  have wf' : ⊢s (.empty :: Δ) := by constructor; assumption
  have f1' := hs_lift_subst_rename .empty f1

  generalize fh : @hs_lift_subst_replace σ Δ Γ .type .empty wf' f2 = f2' at *;
  have ef2 : @hs_lift_subst_replace σ Δ Γ .type .empty wf' f2 = f2' := by
    rw [fh]

  have f3' := hs_lift_subst_stable .empty f3

  apply  @ih2 B' (.empty :: Δ) (^σ) (^σ') f1' f2' f3' _ _ _ cjB wf'
  case _ =>
    intro n y h
    replace f4 := f4 n y
    cases n <;> simp
    case _ => simp at h; assumption
    case _ n =>
      simp at h; unfold Subst.compose; sorry
  case _ =>
    intro n t h
    cases n <;> simp
    case _ => simp at h
    case _ n =>
      generalize zdef : σ n = y at *;
      cases y <;> (simp at h; unfold Subst.compose at h; simp at h; rw[zdef] at h; simp at h)
      case _ a =>
        have f5 := f5 n a zdef; cases f5; case _ t' f5 =>
        simp at f5;
        exists [S] t';
        unfold Subst.compose; simp; rw[f5]
  case _ =>
    intro i t T wt h1 h2 j
    have f6 := f6 i t T wt
    simp at h1; unfold Subst.compose at h1; simp at h1;
    sorry
  simp


theorem compile_beta_kind_type :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : (.kind A::Γ) ⊢τ b : B) ->
  compile_type (.kind A::Γ) b B j1 = .some b' ->
  (j2 : Γ ⊢τ t : A) ->
  compile_type Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by
intro h j1 cj1 j2 cj2 j3;
apply @subst_compile_type b B b' (.kind A :: Γ) Γ (.su t :: I) (.su t' :: I) h
case _ =>
  intro n y h1;
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
case _ =>
  intro n y h1
  cases n <;> simp
  case _ => simp at h1
  case _ => simp at h1; assumption
case _ =>
  intro n t h1
  cases n <;> simp
  case _ n => simp at h1
case _ =>
  intro n t T wt h1 h2 j
  cases n <;> simp at *
  case _ =>
  cases h1; cases h2;
  have u := types_have_unique_kinds j2 j; cases u
  have u := types_have_unique_judgments h j2 j; cases u
  assumption
assumption
apply hs_judgment_ctx_wf .type j2

theorem compile_beta_empty_type :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : (.empty::Γ) ⊢τ b : B) ->
  compile_type (.empty::Γ) b B j1 = .some b' ->
  (j2 : Γ ⊢τ t : A) ->
  compile_type Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by
intro h j1 cj1 j2 cj2 j3;
apply @subst_compile_type b B b' (.empty :: Γ) Γ (.su t :: I) (.su t' :: I) h
case _ =>
  intro n y h1;
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  unfold Frame.get_type at h2; simp at h2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1
case _ =>
  intro n y h1
  cases n <;> simp
  case _ => simp at h1
  case _ => simp at h1; assumption
case _ =>
  intro n t h1
  cases n <;> simp
  case _ n => simp at h1
case _ =>
  intro n t T wt h1 h2 j
  cases n <;> simp at *
  case _ =>
  cases h1; cases h2;
  have u := types_have_unique_kinds j2 j; cases u
  have u := types_have_unique_judgments h j2 j; cases u
  assumption
assumption
apply hs_judgment_ctx_wf .type j2


theorem compile_beta_empty_term :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : (.empty::Γ) ⊢τ b : B) ->
  compile_type (.empty::Γ) b B j1 = .some b' ->
  -- (j2 : Γ ⊢t t : A) ->
  -- compile_term Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by
intro h j1 cj1 /-j2 cj2-/ j3;
apply @subst_compile_type b B b' (.empty :: Γ) Γ (.su t :: I) (.su t' :: I) h
case _ =>
  intro n y h1;
  cases n <;> simp at *; subst h1
  case _ n =>
    rw [Frame.apply_compose]; simp
case _ =>
  intro n s T h1 h2
  cases n <;> simp at *; subst h1
  unfold Frame.get_type at h2; simp at h2
case _ =>
  intro n h1
  cases n <;> simp at *
  rw [Frame.is_stable_stable] at h1
  unfold Frame.is_stable at h1
  simp at h1
case _ =>
  intro n y h1
  cases n <;> simp
  case _ => simp at h1
  case _ => simp at h1; assumption
sorry
case _ =>
  intro n t T wt h1 h2 j
  cases n <;> simp at *
  case _ => cases h1; cases h2; sorry
assumption
case _ => apply hs_judgment_ctx_wf .type j3


def kind_ctx_replace : (k : HsTerm) ->
  Γ ⊢κ k : s ->
  ∀ Γ',  ⊢s Γ' -> Γ' ⊢κ k : s := by
intro k j Γ' wf
cases j
case _ =>
  constructor; assumption
case _ A B jA jB =>
  have lem1 := kind_ctx_replace A jA Γ' wf
  have lem2 := kind_ctx_replace B jB Γ' wf
  constructor;
  assumption; assumption
termination_by h => h.size

theorem compile_kind_replace_empty_lemma Γ' :
  (j1 : Γ ⊢κ k : s) ->
  compile_kind Γ k s j1 = .some τ' ->
  (j2 : Γ' ⊢κ k : s) ->
  compile_kind Γ' k s j2 = .some τ' := by
intro j1 c1 j2
induction Γ, k, s, j1 using compile_kind.induct generalizing Γ' τ'
case _ =>
  cases j2;
  unfold compile_kind at *; assumption
case _ A B h1 h2 ih1 ih2 =>
  cases j2; case _ j2a j2b =>
  unfold compile_kind at c1; simp at c1;
  rw[Option.bind_eq_some] at c1;
  cases c1; case _ A' c1 =>
  cases c1; case _ cA c1 =>
  rw[Option.bind_eq_some] at c1;
  cases c1; case _ B' c1 =>
  cases c1; case _ cB c1 =>
  cases c1
  have ih1' := ih1 Γ' cA j2a
  have ih2' := ih2 Γ' cB j2b
  unfold compile_kind; simp
  rw[Option.bind_eq_some];
  exists A'
  constructor; assumption
  rw[Option.bind_eq_some];
  exists B'


theorem compile_type_replace_empty_lemma : -- (τ k : HsTerm) -> (Γ Γ' : Ctx HsTerm) ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  (Γ d@ n) = .empty ->
  Γ.drop (n + 1) ⊢s f ->
  Γ.modify n (λ _ => f) = Γ' ->
  ⊢s Γ' ->
  (j2 : Γ' ⊢τ τ : k) ->
  compile_type Γ' τ k j2 = .some τ' := by
intro /-τ k Γ Γ'-/ j cj h1 fwf h2 wf j'
induction Γ, τ, k, j using compile_type.induct generalizing Γ' n τ'
case _ => sorry

case _ Γ B f A a j1 j2 j3 j4 ih1 ih2 =>
  unfold compile_type at cj; simp at cj;
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ f' cj =>
  cases cj; case _ cf cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ a' cj =>
  cases cj; case _ ca cj =>
  cases cj
  have j3' := kind_ctx_replace A j3 Γ' wf
  have j4' := kind_ctx_replace B j4 Γ' wf
  have lem2 := hs_replace_type_lemma a A Γ Γ' h1 fwf h2 wf j2
  cases j'; case _ A j3'' j2' j4'' j1' =>
  have u := types_have_unique_kinds j2' lem2; cases u
  have ih1' := @ih1 f' n Γ' cf h1 fwf h2 wf j1'
  have ih2' := @ih2 a' n Γ' ca h1 fwf h2 wf j2'
  have cA' := compile_kind_replace_empty_lemma Γ' j3 cA j3'';
  have cB' := compile_kind_replace_empty_lemma Γ' j4 cB j4'';
  unfold compile_type; simp;
  rw[Option.bind_eq_some]; exists A'
  constructor; assumption
  rw[Option.bind_eq_some]; exists B'
  constructor; assumption
  rw[Option.bind_eq_some]; exists f'
  constructor; assumption
  rw[Option.bind_eq_some]; exists a'

case _ => sorry
case _ => sorry
case _ =>
  sorry



theorem compile_replace_empty :
  Γ ⊢s f ->
  (j1 : (.empty :: Γ) ⊢τ τ : k) ->
  (j2 : (f :: Γ) ⊢τ τ : k) ->
  compile_type (.empty :: Γ) τ k j1 = .some τ' ->
  compile_type (f :: Γ) τ k j2 = .some τ' := by
intro fwf j1 j2 c1
apply compile_type_replace_empty_lemma j1 c1 _ _ _
apply hs_frame_wf_implies_wkn_wf fwf
apply 0
apply f
simp; unfold Frame.apply; simp;
apply fwf
simp
