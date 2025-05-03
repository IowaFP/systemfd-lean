import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Algorithm
import Hs.Metatheory.Uniqueness

set_option maxHeartbeats 1000000

theorem compile_kind_congr :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  B = B' -> k = k' ->
  (sj : Γ ⊢κ B : k) -> (sj' : Γ ⊢κ B' : k') ->
  compile_kind Γ B k sj = compile_kind Γ B' k' sj' := by
intro h e1 e2 sj sj';
subst e1; subst e2;
have u := kinds_have_unique_judgments h sj sj';
subst u; simp;

theorem rename_compile_kind (r : Ren) : (t k : HsTerm) -> (t' : Term) ->
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j : Γ ⊢κ t : k) ->
  compile_kind Γ t k j = .some t' ->
  (wf : ⊢s Δ) ->
  (rctx : ∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  (sj : Δ ⊢κ ([r.to]t) : ([r.to]k)) ->
  compile_kind Δ ([r.to]t) ([r.to]k) sj = .some ([r.to]t') := by
intro t k t' h1 j ck wf h2 sj;
induction Γ, t, k, j using compile_kind.induct generalizing Δ t' <;> simp
case _ =>
  unfold compile_kind at ck; cases ck
  cases sj; simp;
  unfold compile_kind; rfl
case _ Γ A B j1 j2 ih1 ih2 =>
  unfold compile_kind at ck; simp at ck;
  rw[Option.bind_eq_some] at ck;
  cases ck; case _ A' ck =>
  cases ck; case _ cA ck =>
  rw[Option.bind_eq_some] at ck;
  cases ck; case _ B' ck =>
  cases ck; case _ cB ck =>
  cases ck
  simp at sj; cases sj; case _ jA' jB' =>
  unfold compile_kind; simp
  have ih1' := @ih1 Δ A' cA wf h2 jA'
  have ih2' := @ih2 Δ B' cB wf h2 jB'
  cases sj; simp;
  rw[Option.bind_eq_some]; exists ([r.to]A')
  constructor;
  case _ =>
    rw[<-ih1']
    apply compile_kind_congr h1
    unfold Subst.apply; simp
    simp
  rw[Option.bind_eq_some]; exists ([r.to]B')
  constructor;
  case _ =>
    rw[<-ih2']
    apply compile_kind_congr h1
    unfold Subst.apply; simp
    simp
  simp


theorem weaken_compile_kind f :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j : Γ ⊢κ t : k) ->
  compile_kind Γ t k j = .some t' ->
  Γ ⊢s f ->
  (sj : (f :: Γ) ⊢κ ([S]t) : ([S]k)) ->
  compile_kind (f::Γ) ([S]t) ([S]k) sj = .some ([S]t') := by
intro wfeq j c h;
apply rename_compile_kind (λ x => (x + 1)) _ _ _ wfeq j c;
case _ => apply hs_frame_wf_implies_wkn_wf h
case _ =>
  intro x; simp;
  generalize fh : Γ d@ x = f at *;
  cases f
  all_goals try (unfold Frame.apply; simp; congr)
  unfold Frame.apply; simp
  all_goals(constructor; unfold S; congr; unfold S; congr)

theorem compile_type_congr :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  B = B' -> k = k' ->
  (sj : Γ ⊢τ B : k) -> (sj' : Γ ⊢τ B' : k') ->
  compile_type Γ B k sj = compile_type Γ B' k' sj' := by
intro h e1 e2 sj sj';
subst e1; subst e2;
have u := types_have_unique_judgments h sj sj';
subst u; simp;

theorem rename_compile_type (r : Ren) : (t k : HsTerm) -> (t' : Term) ->
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j : Γ ⊢τ t : k) ->
  compile_type Γ t k j = .some t' ->
  (wf : ⊢s Δ) ->
  (rctx : ∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  (sj : Δ ⊢τ ([r.to]t) : ([r.to]k)) ->
  compile_type Δ ([r.to]t) ([r.to]k) sj = .some ([r.to]t') := by
intro t k t' h1 j cj wf h2 sj -- sjR;
induction Γ, t, k, j using compile_type.induct generalizing Δ t' r
all_goals (unfold compile_type at cj; simp at cj)
case _ Γ T x wf' c gt jk  =>
  have j : Γ ⊢τ `#x : T := by constructor; assumption; assumption; assumption; assumption
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ T' cj =>
  cases cj; case _ cT cj =>
  cases cj;
  unfold compile_type; simp;
  have sj' := @hs_rename Γ Δ r .type (`#x, T) j wf h2
  have u := types_have_unique_judgments h1 sj' sj
  subst u; cases sj'; case _ wf c' jk' gt' =>
  simp;
  rw[Option.bind_eq_some];
  exists ([r.to]T')
  constructor;
  case _ =>
    apply @rename_compile_kind Γ Δ r T `□
    assumption
    assumption
    assumption
    assumption
  simp; unfold Ren.to; simp;
case _ Γ B f A a j1 j2 j3 j4 ih1 ih2 =>
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
  cases sj; case _ α jka ja' jbk jb' =>
  unfold compile_type; simp;
  have j2' := @hs_rename Γ Δ r .type (a, A) j2 wf h2; simp at j2';
  have j1' := @hs_rename Γ Δ r .type (f, (A `-k> B)) j1 wf h2; simp at j1'
  have u1 := kinds_subst_eff_free_types (r.to) (A `-k> B) j1; simp at u1;
  have ua := idempotent_substitution_typing r.to A j2;
  have u := types_have_unique_judgments h1 ja'
  have ih1' := @ih1 Δ r f' cf wf h2 j1'
  have ih2' := @ih2 Δ r a' ca wf h2 j2'
  have uα : α = [r.to]A := by
    unfold Subst.apply at j2';
    have u := types_have_unique_kinds ja' j2';
    rw[u]; simp; unfold Subst.apply; simp;
  rw[Option.bind_eq_some]; exists ([r.to]A')
  constructor;
  case _ =>
    subst uα;
    apply @rename_compile_kind Γ Δ r A `□;
    assumption
    assumption
    assumption
    assumption
  rw[Option.bind_eq_some]; exists ([r.to]B')
  constructor;
  case _ =>
    apply @rename_compile_kind Γ Δ r B `□;
    assumption
    assumption
    assumption
    assumption
  rw[Option.bind_eq_some]; exists ([r.to]f')
  constructor;
  case _ =>
    rw[<-ih1']
    apply compile_type_congr h1
    unfold Subst.apply; simp
    simp; assumption
  rw[Option.bind_eq_some]; exists ([r.to]a')
  constructor;
  case _ =>
    rw[<-ih2']
    apply compile_type_congr h1
    unfold Subst.apply; simp
    assumption
  simp

case _ Γ A B j1 j2 ih =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  cases cj;
  cases sj; case _ sjA sjB =>
  simp;
  have sjB' := sjB;
  rw[<-@HsTerm.subst_const r.lift.to] at sjB'
  rw[<-Subst.lift_lemma] at sjB';
  have wf' : ⊢s (.kind ([r.to]A) :: Δ) := by constructor; assumption; assumption
  have h2' := hs_rename_lift r (.kind A) h2
  have h3 := @rename_compile_kind Γ Δ r A `□ A' h1 j1 cA wf h2 sjA
  have ih := @ih (.kind ([r.to]A) :: Δ) (Ren.lift r) B' cB wf' h2' sjB'
  unfold compile_type; simp;
  rw[Option.bind_eq_some]
  exists ([r.to] A')
  constructor; assumption
  rw[Option.bind_eq_some]
  exists ([^r.to] B')
  constructor;
  have e : `★ = [r.lift.to] `★ := by simp
  have u1 : [r.lift.to]B' = [^r.to]B' := by congr; rw[Subst.lift_lemma]
  rw[u1] at ih; rw[<-ih];
  apply compile_type_congr h1;
  have u2 : HsTerm.smap Subst.lift (^r.to) B = [r.lift.to]B := by
    rw[Subst.lift_lemma]; unfold Subst.apply; simp
  apply u2
  apply e
  simp

case _ Γ A B j1 j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  cases cj;
  cases sj; case _ sjA sjB =>
  simp;
  have sjB' := sjB;
  rw[<-@HsTerm.subst_const r.lift.to] at sjB'
  rw[<-Subst.lift_lemma] at sjB';
  have wf' : ⊢s (.empty :: Δ) := by constructor; assumption
  have h2' := hs_rename_lift r .empty h2
  have ih1' := @ih1 Δ r A' cA wf h2 sjA
  have ih2' := @ih2 (.empty :: Δ) (Ren.lift r) B' cB wf' h2' sjB'
  unfold compile_type; simp;
  rw[Option.bind_eq_some]
  exists ([r.to] A')
  constructor; assumption
  rw[Option.bind_eq_some]
  exists ([^r.to] B')
  constructor;
  have e : `★ = [r.lift.to] `★ := by simp
  have u1 : [r.lift.to]B' = [^r.to]B' := by congr; rw[Subst.lift_lemma]
  rw[u1] at ih2'; rw[<-ih2'];
  apply compile_type_congr h1;
  have u2 : HsTerm.smap Subst.lift (^r.to) B = [r.lift.to]B := by
    rw[Subst.lift_lemma]; unfold Subst.apply; simp
  apply u2
  apply e
  simp

case _ Γ A B j1 vhv j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ A' cj =>
  cases cj; case _ cA cj =>
  rw[Option.bind_eq_some] at cj;
  cases cj; case _ B' cj =>
  cases cj; case _ cB cj =>
  cases cj;
  cases sj; case _ sjA vhv' sjB =>
  simp;
  have sjB' := sjB;
  rw[<-@HsTerm.subst_const r.lift.to] at sjB'
  rw[<-Subst.lift_lemma] at sjB';
  have wf' : ⊢s (.empty :: Δ) := by constructor; assumption
  have h2' := hs_rename_lift r .empty h2
  have ih1' := @ih1 Δ r A' cA wf h2 sjA
  have ih2' := @ih2 (.empty :: Δ) (Ren.lift r) B' cB wf' h2' sjB'
  unfold compile_type; simp;
  rw[Option.bind_eq_some]
  exists ([r.to] A')
  constructor; assumption
  rw[Option.bind_eq_some]
  exists ([^r.to] B')
  constructor;
  have e : `★ = [r.lift.to] `★ := by simp
  have u1 : [r.lift.to]B' = [^r.to]B' := by congr; rw[Subst.lift_lemma]
  rw[u1] at ih2'; rw[<-ih2'];
  apply compile_type_congr h1;
  have u2 : HsTerm.smap Subst.lift (^r.to) B = [r.lift.to]B := by
    rw[Subst.lift_lemma]; unfold Subst.apply; simp
  apply u2
  apply e
  simp

theorem weaken_compile_type :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j : Γ ⊢τ t : k) ->
  compile_type Γ t k j = .some t' ->
  Γ ⊢s f ->
  (sj : (f :: Γ) ⊢τ ([S]t) : ([S]k)) ->
  compile_type (f :: Γ) ([S]t) ([S]k) sj = .some ([S]t') := by
intro wfeq j c h sj;
apply rename_compile_type (λ x => (x + 1)) _ _ _ wfeq j c;
case _ => apply hs_frame_wf_implies_wkn_wf h
case _ =>
  intro x; simp;
  generalize fh : Γ d@ x = f at *;
  cases f
  all_goals try (unfold Frame.apply; simp; congr)
  unfold Frame.apply; simp
  all_goals(constructor; unfold S; congr; unfold S; congr)
