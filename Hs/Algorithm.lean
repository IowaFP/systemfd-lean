import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm

@[simp]
def compile_ctor2variant : HsCtor2Variant -> Ctor2Variant
| .arrowk => .arrowk

@[simp]
def compile_ctor3variant : HsCtor3Variant -> Ctor2Variant
| .appk => .appk
| .appt => .appt
| .app => .app

@[simp]
def compile_bind2variant : HsBind2Variant -> Bind2Variant
| .all => .all
| .arrow => .arrow
| .farrow => .arrow
| .lam => .lam
| .lamt => .lamt

-- TODO: move bind2_frame and hs_bind2_frame in a common place
@[simp]
def hs_bind2_frame : Term -> HsBind2Variant -> Frame Term
| t, .all => .kind t
| t, .lam => .type t
| t, .lamt => .kind t
| _ , _ =>  .empty

def synth_term : Ctx Term -> Term -> Option Term := sorry
def perform_black_magic : Ctx Term -> Term -> Option Term := sorry

-- @[simp]
def compile : (Γ : Ctx Term) -> (τ : HsTerm) -> (t : HsTerm) -> Option Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , `□, `★ => .some ★

| Γ, `□ , .HsCtor2 .arrowk t1 t2 => do
  let t1' <- compile Γ `□ t1
  let t2' <- compile Γ `□ t2
  .some (.ctor2 .arrowk t1' t2')

| Γ, `★ , .HsBind2 .arrow A B => do
  let A' <- compile Γ `□ A
  let B' <- compile Γ `□ B
  .some (.bind2 .arrow A' B')

| Γ, `★ , .HsBind2 .all A B => do
  let A' <- compile Γ `□ A
  let B' <- compile (.kind A' :: Γ) `★ B
  .some (.bind2 .all A' B')


| Γ, .HsBind2 .arrow A B, .HsBind2 .lam A' t => do
  if A == A'
  then do
    let α <- compile Γ `★ A
    let t' <- compile (.type α :: Γ) B t
    .some (.bind2 .lam α t')
  else .none

| Γ, .HsBind2 .all A B, .HsBind2 .lamt A' t => do
  if A == A'
  then do
    let α <- compile Γ `□ A
    let t' <- compile (.kind α :: Γ) B t
    .some (.bind2 .lamt α t')
  else .none

-- | Γ, .HsBind2 .farrow A B, t => do
--   let α <- compile Γ `★ A
--   let d <- synth_term Γ α
--   let t' <- compile (.term α d :: Γ) B t -- Deal with debrujin BS
--   .some (.bind2 .lam α t')


| Γ, τ, .HsLet A t1 t2 => do
  let α <- compile Γ `★ A
  let t1' <- compile Γ A t2
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .some (.letterm α t1' t2')

-- | Γ, τ, .HsIte p s i t => do
--   let p' <- compile Γ sorry p
--   let s' <- compile Γ sorry s
--   let i' <- compile Γ sorry i
--   let t' <- compile Γ τ t
--   .some (.ite p' s' i' t')

-------------------
--- Term
-------------------
| Γ, τ, `#x => .some #x
  -- is this a type variable or a term variable?
  -- if (Γ d@ x).is_term_var
  -- then do
  --   let τ' <- compile Γ `★ τ
  --   -- let η <- perform_black_magic Γ τ' -- How do i even know how to perform_black_magic here?
  --   .some (#x) -- ▹ η)
  -- else .some #x

| _ , _, _  => .none

decreasing_by repeat sorry
