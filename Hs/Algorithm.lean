import Hs.HsJudgment
import Hs.HsTerm
import SystemFD.Term

def compile (Γ : Ctx HsTerm) (t : HsTerm) (τ : HsTerm) : Γ ⊢s t : τ -> Option Term
-----------------------------
----- Types and kinds
-----------------------------
| .ax _ => some ★
| @HsJudgment.arrowk Γ A B j1 j2 => do
  let t1 <- compile Γ A `□ j1
  let t2 <- compile Γ B `□ j2
  .some (t1 -k> t2)
| @HsJudgment.appk Γ f A B a j1 j2 => do
  let t1 <- compile Γ f (A `-k> B) j1
  let t2 <- compile Γ a A j2
  .some (t1 `@k t2)
| @HsJudgment.allt Γ A B j1 j2 => do
  let t1 <- compile Γ A `□ j1
  let t2 <- compile (.kind A :: Γ) B `★ j2
  .some (∀[t1] t2)
| @HsJudgment.arrow Γ A B j1 j2 => do
  let t1 <- compile Γ A `★ j1
  let t2 <- compile (.empty ::Γ) B `★ j2
  .some (t1 -t> t2)
| @HsJudgment.farrow Γ A B j1 _ j2 => do
  let t1 <- compile Γ A `★ j1
  let t2 <- compile (.empty ::Γ) B `★ j2
  .some (t1 -t> t2)

--------------------------------------------
----- terms
-----------------------------------------
| @HsJudgment.var _ x _ _ _ => #x
| @HsJudgment.lam Γ A t B j1 j2 _ => do
  let A' <- compile Γ A `★ j1
  let t' <- compile (.type A :: Γ) t B j2
  .some (`λ[A'] t')
| @HsJudgment.app Γ t1 A B t2 B' j1 j2 _ => do
  let t1' <- compile Γ t1 (A → B) j1
  let t2' <- compile Γ t2 A j2
  .some (t1' `@ t2')
| @HsJudgment.hslet Γ A t1 t2 B _ j1 j2 j3 j4 => do
  let A' <- compile Γ  A `★ j1
  let t1' <- compile Γ t1 A j2
  let t2' <- compile (.term A t1 :: Γ) t2 ([S]B) j3
  .some (.letterm A' t1' t2')
| @HsJudgment.hsIte Γ p A s R i B t T j1 j2 j3 j4 _ _ _ _ _ _  => do
  let p' <- compile Γ p A j1
  let s' <- compile Γ s R j2
  let i' <- compile Γ i B j3
  let t' <- compile Γ t T j4
  .some (.ite p' s' i' t')
----------------------------------------
--- Implicit
--------------------------------------
| @HsJudgment.implicitAllE _ _ _ _ _ _ _  => .none
  -- let t1 <- (compile Γ t _ j1)
  -- let t2 <- (compile Γ e _ j2)
  -- .some (t1 `@t t2)
| @HsJudgment.implicitAllI Γ A t τ j1 j2 j3 => .none
  -- do
  -- let j1' := HsJudgment.implicitAllI j1 j2 j3
  -- let t' <- compile Γ t (`∀{A}τ) j1'
  -- .some t'
| @HsJudgment.implicitArrI Γ π t τ e j1 j2 j3 j4 => .none  -- do
  -- let j1' : Γ ⊢s (π ⇒ τ) : `★ := HsJudgment.farrow j1 j2 sorry
  -- let j2' : Γ ⊢s t : (π ⇒ τ) := HsJudgment.lam j1 j2 j1'
  -- let π' <- compile Γ π `★ j1
  -- let t' <- compile Γ t (π ⇒ τ) j2'
  -- .some (`λ[π'] t')
| @HsJudgment.implicitArrE Γ t π τ e j1 j2 => do
  -- let t' <- compile Γ t (π ⇒ τ) j1
  -- let e' <- compile Γ e π j2
  -- .some (t' `@ e')
  .none
