import Surface.Ty
import Core.Ty
import Core.Global

def trans_ki : Surface.Kind -> Kind
| .base .closed => .base .closed
| .base .open => .base .open
| .arrow k1 k2 => .arrow (trans_ki k1) (trans_ki k2)

@[simp]
def trans_ty (G : List Global) (Δ : List Kind) : Surface.Ty -> Option Ty
| .var x => return .var x
| .global x => return .global x
| .arrow a b => do
  let a' <- trans_ty G Δ a
  let b' <- trans_ty G Δ b
  return .arrow  a' b'
| .app a b => do
  let a' <- trans_ty G Δ a
  let b' <- trans_ty G Δ b
  return .app a' b'
| .all k p => do
  let k' := trans_ki k
  let p' <- trans_ty G (k' :: Δ) p
  return .all k' p'
