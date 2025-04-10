import Hs.HsJudgment
import Hs.HsTerm
import SystemFD.Term
import SystemFD.Algorithm

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
-- TODO: What if we just return the compiled type with the compiled term?
| @HsJudgment.varTy _ x T _ _ _ j => do
  let _ <- compile_kind Γ T `□ j
  .some #x
| @HsJudgment.appk Γ f A B a j1 j2 j3 j4 => do
  let _ <- compile_kind Γ A `□ j3
  let _ <- compile_kind Γ B `□ j4
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
| @HsJudgment.implicitAllE Γ A τ t e j1 j2 j3 j4 => do
  let _ <- compile_type Γ (`∀{A}τ) `★ j1
  let _ <- compile_kind Γ A `□ j2
  let t1 <- (compile_term Γ t (`∀{A}τ) j3)
  let t2 <- (compile_type Γ e A j4)
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
| kind : HsCtx Γ -> (Γ ⊢κ k : `□) -> HsCtx (.kind k :: Γ)
| datatype : HsCtx Γ -> (Γ ⊢κ k : `□) -> HsCtx (.datatype k :: Γ)
| type : HsCtx Γ -> (Γ ⊢τ τ : `★) -> HsCtx (.type τ :: Γ)
| ctor : HsCtx Γ -> (Γ ⊢τ τ : `★) -> HsCtx (.ctor τ :: Γ)
| openm : HsCtx Γ -> (Γ ⊢τ τ : `★) -> HsCtx (.openm τ :: Γ)

@[simp]
def compile_ctx : HsCtx Γ -> Option (Ctx Term)
| .nil => .some []
| .empty Γ => do
  let Δ <- compile_ctx Γ
  let _ <- wf_ctx Δ
  .some (.empty :: Δ)
| @HsCtx.kind Γ k Γ' j => do
  let Δ <- compile_ctx Γ'
  let _ <- wf_ctx Δ
  let τ <- compile_kind Γ k `□ j
  .some (.kind τ :: Δ)
| @HsCtx.datatype Γ t Γ' j => do
  let Δ <- compile_ctx Γ'
  let _ <- wf_ctx Δ
  let τ <- compile_kind Γ t `□ j
  .some (.datatype τ :: Δ)
| @HsCtx.type Γ t Γ' j => do
  let Δ <- compile_ctx Γ'
  let _ <- wf_ctx Δ
  let τ <- compile_type Γ t `★ j
  .some (.type τ :: Δ)
| @HsCtx.ctor Γ t Γ' j => do
  let Δ <- compile_ctx Γ'
  let _ <- wf_ctx Δ
  let τ <- compile_type Γ t `★ j
  .some (.ctor τ :: Δ)
| @HsCtx.openm Γ t Γ' j => do
  let Δ <- compile_ctx Γ'
  let _ <- wf_ctx Δ
  let τ <- compile_type Γ t `★ j
  .some (.openm τ :: Δ)


@[simp]
abbrev CompileArgs : (HsVariant) -> (Ctx HsTerm) -> Type
| .ctx => λ Γ => HsCtx Γ -> Option (Ctx Term)
| .kind => λ Γ => (p : HsTerm × HsTerm) × HsJudgment .kind Γ p -> Option Term
| .type => λ Γ => (p : HsTerm × HsTerm) × HsJudgment .type Γ p -> Option Term
| .term =>  λ Γ => (p : HsTerm × HsTerm) × HsJudgment .term Γ p -> Option Term


def compile : (v : HsVariant) -> (Γ : Ctx HsTerm) -> CompileArgs v Γ
| .ctx => λ _ => λ ctx => compile_ctx ctx
| .kind => λ Γ => λ ⟨p, j⟩ => compile_kind Γ p.fst p.snd j
| .type => λ Γ => λ ⟨p, j⟩ => compile_type Γ p.fst p.snd j
| .term =>  λ Γ => λ ⟨p, j⟩ => compile_term Γ p.fst p.snd j
