import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import Hs.Monad

@[simp]
def compile_ctor2variant : HsCtor2Variant -> Ctor2Variant
| .arrowk => .arrowk
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


@[simp]
def compile_spine_variant : HsSpineVariant -> SpineVariant
| .term => .term
| .type => .type
| .kind => .kind


@[simp]
def compile_kind (Γ : Ctx Term) : Term -> HsTerm -> DsM Term
  | □, `★ => .ok ★
  | □, (k1 `-k> k2) => do
    let k1' <- compile_kind Γ □ k1
    let k2' <- compile_kind Γ □ k2
    return k1' -k> k2'
  | τ , t => .error ("comile kind failed" ++ repr τ ++ repr t)
