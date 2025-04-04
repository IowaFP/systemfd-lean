import Hs.HsJudgment
import Hs.HsTerm
import SystemFD.Term

def compile_kind (Γ : Ctx HsTerm) (κ : HsTerm) (ty : HsTerm) : Γ ⊢κ κ : ty -> Option Term
| .ax _ => some ★
| @HsJudgment.arrowk Γ A B j1 j2 => do
  let t1 <- compile_kind Γ A `□ j1
  let t2 <- compile_kind Γ B `□ j2
  .some (t1 -k> t2)

def compile_type (Γ : Ctx HsTerm) (τ : HsTerm) (k : HsTerm) : Γ ⊢τ τ : k -> Option Term
-----------------------------
----- Types and kinds
-----------------------------
| @HsJudgment.varTy _ x _ _ _ _ => .some #x
| @HsJudgment.appk Γ f A B a j1 j2 => do
  let t1 <- compile_type Γ f (A `-k> B) j1
  let t2 <- compile_type Γ a A j2
  .some (t1 `@k t2)
| @HsJudgment.allt Γ A B j1 j2 => do
  let t1 <- compile_kind Γ A `□ j1
  let t2 <- compile_type (.kind A :: Γ) B `★ j2
  .some (∀[t1] t2)
| @HsJudgment.arrow Γ A B j1 j2 => do
  let t1 <- compile_type Γ A `★ j1
  let t2 <- compile_type (.empty ::Γ) B `★ j2
  .some (t1 -t> t2)
| @HsJudgment.farrow Γ A B j1 _ j2 => do
  let t1 <- compile_type Γ A `★ j1
  let t2 <- compile_type (.empty ::Γ) B `★ j2
  .some (t1 -t> t2)


def compile_term (Γ : Ctx HsTerm) (t : HsTerm) (τ : HsTerm) : Γ ⊢t t : τ -> Option Term
--------------------------------------------
----- terms
-----------------------------------------
| @HsJudgment.var _ x _ _ _ _ => #x
| @HsJudgment.lam Γ A t B j1 j2 _ => do
  let A' <- compile_type Γ A `★ j1
  let t' <- compile_term (.type A :: Γ) t B j2
  .some (`λ[A'] t')
| @HsJudgment.app Γ t1 A B t2 B' j1 j2 _ => do
  let t1' <- compile_term Γ t1 (A → B) j1
  let t2' <- compile_term Γ t2 A j2
  .some (t1' `@ t2')
| @HsJudgment.hslet Γ A t1 t2 B j1 j2 j3 j4 => do
  let A' <- compile_type Γ  A `★ j1
  let t1' <- compile_term Γ t1 A j2
  let t2' <- compile_term (.term A t1 :: Γ) t2 ([S]B) j3
  .some (.letterm A' t1' t2')
| @HsJudgment.hsIte Γ p A s R i B t T j1 j2 j3 j4 _ _ _ _ _ _  => do
  let p' <- compile_term Γ p A j1
  let s' <- compile_term Γ s R j2
  let i' <- compile_term Γ i B j3
  let t' <- compile_term Γ t T j4
  .some (.ite p' s' i' t')

----------------------------------------
--- Implicit
----------------------------------------
| @HsJudgment.implicitAllE Γ t A τ e j1 j2  => do
  let t1 <- (compile_term Γ t (`∀{A}τ) j1)
  let t2 <- (compile_term Γ e A j2)
  .some (t1 `@t t2)
| @HsJudgment.implicitAllI Γ A t τ j1 j2 j3 => do
  let t' <- compile_term (.kind A :: Γ) t τ j1
  let A' <- compile_kind Γ A `□ j2
  .some (Λ[A']t')
| @HsJudgment.implicitArrI Γ π τ t j1 j2 _ j3 => do
  let π' <- compile_type Γ π `★ j1
  let t' <- compile_term (.type π :: Γ) t τ j3
  .some (`λ[π'] t')
| @HsJudgment.implicitArrE Γ t π τ e j1 j2 => do
  let t' <- compile_term Γ t (π ⇒ τ) j1
  let e' <- compile_term Γ e π j2
  .some (t' `@ e')
termination_by h => h.size

@[aesop safe [constructors, cases]]
inductive HsCtx : Ctx HsTerm -> Type where
| nil : HsCtx []
| empty : HsCtx Γ -> HsCtx (.empty::Γ)
| kind : HsCtx Γ -> (k : HsTerm) × (Γ ⊢κ k : `□) -> HsCtx (.kind k :: Γ)
| datatype : HsCtx Γ -> (k : HsTerm) × (Γ ⊢κ k : `□) -> HsCtx (.datatype k :: Γ)
| type : HsCtx Γ -> (τ : HsTerm) × (Γ ⊢τ τ : `★) -> HsCtx (.type τ :: Γ)
| ctor : HsCtx Γ -> (τ : HsTerm) × (Γ ⊢τ τ : `★) -> HsCtx (.ctor τ :: Γ)
| openm : HsCtx Γ -> (τ : HsTerm) × (Γ ⊢τ τ : `★) -> HsCtx (.ctor τ :: Γ)

@[simp]
def compile_ctx : HsCtx Γ -> Option (Ctx Term)
| .nil => .some []
| .empty Γ => do
  let Γ' <- compile_ctx Γ
  .some (.empty :: Γ')
| @HsCtx.kind Γ _ Γ' ⟨t, j⟩ => do
  let Δ <- compile_ctx Γ'
  let τ <- compile_kind Γ t `□ j
  .some (.kind τ :: Δ)
| @HsCtx.datatype Γ _ Γ' ⟨t, j⟩ => do
  let Δ <- compile_ctx Γ'
  let τ <- compile_kind Γ t `□ j
  .some (.datatype τ :: Δ)
| @HsCtx.type Γ _ Γ' ⟨t, j⟩ => do
  let Δ <- compile_ctx Γ'
  let τ <- compile_type Γ t `★ j
  .some (.type τ :: Δ)
| @HsCtx.ctor Γ _ Γ' ⟨t, j⟩ => do
  let Δ <- compile_ctx Γ'
  let τ <- compile_type Γ t `★ j
  .some (.ctor τ :: Δ)
| @HsCtx.openm Γ _ Γ' ⟨t, j⟩ => do
  let Δ <- compile_ctx Γ'
  let τ <- compile_type Γ t `★ j
  .some (.openm τ :: Δ)
