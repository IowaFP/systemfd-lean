import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm


def compile_ctor2variant : HsCtor2Variant -> Ctor2Variant
| .arrowk => .arrowk
| .appk => .appk
| .appt => .appt
| .app => .app

def compile_bind2variant : HsBind2Variant -> Bind2Variant
| .all => .all
| .arrow => .arrow
| .farrow => .arrow
| .lam => .lam
| .lamt => .lamt

-- TODO: move bind2_frame and hs_bind2_frame in a common place
def hs_bind2_frame : Term -> HsBind2Variant -> Frame Term
| t, .all => .kind t
| t, .lam => .type t
| t, .lamt => .kind t
| _ , _ =>  .empty


def compile : (Γ : Ctx Term) -> (t : HsTerm) -> Option Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , `★ => .some ★
| Γ, .HsCtor2 .arrowk k1 k2 => do
  let k1' <- compile Γ k1
  let k2' <- compile Γ k2
  .some (k1' -k> k2')


| Γ, .HsCtor2 v t1 t2 => do
  let v' := compile_ctor2variant v
  let t1' <- compile Γ t1
  let t2' <- compile Γ t2
  .some (.ctor2 v' t1' t2')

| Γ, .HsBind2 v t1 t2 => do
  let v' := compile_bind2variant v
  let t1' <- compile Γ t1
  let t2' <- compile (hs_bind2_frame t1' v :: Γ) t2
  .some (.bind2 v' t1' t2')

| Γ, .HsLet t1 t2 t3 => do
  let t1' <- compile Γ t1
  let t2' <- compile Γ t2
  let t3' <- compile Γ t3
  .some (.letterm t1' t2' t3')

| Γ, .HsIte t1 t2 t3 t4 => do
  let t1' <- compile Γ t1
  let t2' <- compile Γ t2
  let t3' <- compile Γ t3
  let t4' <- compile Γ t4
  .some (.ite t1' t2' t3' t4')

-------------------
--- Term
-------------------
| _, `#x => #x

| _ , _  => .none
