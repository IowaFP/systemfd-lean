import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Algorithm
import Hs.Metatheory.Uniqueness

set_option maxHeartbeats 1000000

theorem weaken_compile_kind f :
  (j : Γ ⊢κ t : k) ->
  (sj : (f :: Γ) ⊢κ ([S]t) : ([S]k)) ->
  compile_kind Γ t k j = .some t' ->
  compile_kind (f::Γ) ([S]t) ([S]k) sj = .some ([S]t') := by
intro j sj c;
induction Γ, t, k, j using compile_kind.induct generalizing t';
case _ =>
  unfold compile_kind; cases sj; simp; unfold compile_kind at c; cases c; simp;
case _ j1 j2 ih1 ih2 =>
  unfold compile_kind at c; simp at c;
  rw[Option.bind_eq_some] at c;
  cases c; case _ wa c =>
  cases c; case _ ca cb =>
  rw[Option.bind_eq_some] at cb;
  cases cb; case _ wb cb =>
  cases cb; case _ cb e =>
  cases e; cases sj;
  case _ jaw jbw =>
  have ih1' := @ih1 wa jaw ca
  have ih2' := @ih2 wb jbw cb
  unfold compile_kind; simp;
  rw[Option.bind_eq_some];
  exists ([S]wa); apply And.intro;
  assumption;
  rw[Option.bind_eq_some];
  exists ([S]wb);


theorem weaken_compile_type :
  (∀ (Γ : Ctx HsTerm) (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j : Γ ⊢τ t : k) ->
  compile_type Γ t k j = .some t' ->
  Γ ⊢s f ->
  (sj : (f :: Γ) ⊢τ ([S]t) : ([S]k)) ->
  compile_type (f :: Γ) ([S]t) ([S]k) sj = .some ([S]t') := by
intro wfeq j c h sj;
induction Γ, t, k, j using compile_type.induct generalizing f t' <;> simp at *;
case _ =>
  unfold compile_type; cases sj; simp;
  unfold compile_type at c; simp at c;
  rw[Option.bind_eq_some] at c;
  cases c; case _ wa c =>
  cases c; case _ ca cb =>
  cases cb; simp
  rw[Option.bind_eq_some];
  exists ([S]wa); simp;
  case _ j _ _ sj _ =>
    apply weaken_compile_kind f j sj ca;
case _ Γ B fa A a j1 j2 j3 j4 ih1 ih2 =>
  unfold compile_type at c; simp at c
  rw[Option.bind_eq_some] at c;
  cases c; case _ wA c =>
  cases c; case _ cA cb =>
  rw[Option.bind_eq_some] at cb;
  cases cb; case _ wB cb =>
  cases cb; case _ cB cf =>
  rw[Option.bind_eq_some] at cf;
  cases cf; case _ wf cf =>
  cases cf; case _ cf ca =>
  rw[Option.bind_eq_some] at ca;
  cases ca; case _ wa ca =>
  cases ca; case _ ca e =>
  cases e;
  have wf' := Ctx.hs_weaken_frame (hs_judgment_ctx_wf .kind j3) h
  have lem1 : (f :: Γ) ⊢τ ([S]fa) : ([S](A `-k> B)) := by
    apply hs_weaken_type;
    assumption
    assumption

  unfold compile_type; cases sj; simp;
  rw[Option.bind_eq_some]; case _ A' jA' ja' jB' jb' =>
  have sj3 := hs_weaken_kind wf' j3
  have sj2 := hs_weaken_type wf' j2
  have u := types_have_unique_kinds ja' sj2; cases u
  have u := types_have_unique_judgments wfeq lem1 jb'; cases u
  exists ([S]wA);
  constructor
  case _ => apply weaken_compile_kind f j3 jA' cA
  rw[Option.bind_eq_some]; exists ([S]wB)
  constructor
  case _ => apply weaken_compile_kind f j4 jB' cB
  rw[Option.bind_eq_some]; exists ([S]wf)
  constructor
  case _ =>
    have ih1' := ih1 cf h lem1
    assumption
  rw[Option.bind_eq_some]; exists ([S]wa)
  constructor
  case _ =>
    have ih2' := ih2 ca h ja'
    assumption
  rfl

case _ Γ A B j1 j2 ih =>
  unfold compile_type at c; simp at c
  rw[Option.bind_eq_some] at c;
  cases c; case _ wA c =>
  cases c; case _ cA cb =>
  rw[Option.bind_eq_some] at cb;
  cases cb; case _ wB cb =>
  cases cb; case _ cB cf =>
  cases cf;
  cases sj; case _ j1' j2' =>

  unfold compile_type; simp;
  rw[Option.bind_eq_some]; exists ([S]wA)
  constructor;
  case _ => apply weaken_compile_kind f j1 j1' cA;
  rw[Option.bind_eq_some]; exists ([^S]wB)
  constructor;
  case _ =>
    have ih' := @ih wB f cB
    sorry
  simp;
case _ j1 j2 ih1 ih2 =>
  unfold compile_type at c; simp at c;
  rw[Option.bind_eq_some] at c;
  cases c; case _ wa c =>
  cases c; case _ ca cb =>
  rw[Option.bind_eq_some] at cb;
  cases cb; case _ wb cb =>
  cases cb; case _ cb e =>
  cases e;
  cases sj; case _ ja jb =>
  unfold compile_type; simp;

  rw[Option.bind_eq_some];
  exists ([S]wa);
  constructor
  case _ ja =>
    sorry
  rw[Option.bind_eq_some];
  exists ([^S]wb)
  constructor
  sorry
  simp

case _ => sorry
