import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Algorithm

set_option maxHeartbeats 1000000

theorem weaken_compile_kind :
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
  (j : Γ ⊢τ t : k) ->
  (sj : (f :: Γ) ⊢τ ([S]t) : ([S]k)) ->
  compile_type Γ t k j = .some t' ->
  compile_type (f::Γ) ([S]t) ([S]k) sj = .some ([S]t') := by
intro j sj c;
induction Γ, t, k, j using compile_type.induct generalizing t' <;> simp at *;
case _ =>
  unfold compile_type; cases sj; simp; unfold compile_type at c; cases c; simp
case _ => sorry
case _ => sorry
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
  apply And.intro;
  case _ ja =>
    sorry
  rw[Option.bind_eq_some];
  exists ([^S]wb)
  apply And.intro
  sorry
  simp
case _ => sorry
