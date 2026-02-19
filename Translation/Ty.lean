import Surface.Ty
import Core.Ty
import Core.Global

@[simp]
def Surface.Kind.translate : Surface.Kind -> Core.Kind
| .base .closed => .base .closed
| .base .open => .base .open
| .arrow k1 k2 => .arrow (translate k1) (translate k2)

def Surface.Kind.translateEnv : List Surface.Kind -> List Core.Kind := List.map (translate ·)

@[simp]
def Surface.Ty.translate (G : List Core.Global) (Δ : List Core.Kind) : Surface.Ty -> Option Core.Ty
| .var x => return .var x
| .global x => return .global x
| .arrow a b => do
  let a' <-  a.translate G Δ
  let b' <- b.translate G Δ
  return .arrow  a' b'
| .app a b => do
  let a' <- a.translate G Δ
  let b' <- b.translate G Δ
  return .app a' b'
| .all k p => do
  let k' := k.translate
  let p' <- p.translate G (k' :: Δ)
  return .all k' p'

def Surface.Ty.translateEnv (G : List Core.Global) (Δ : List Core.Kind) :
  List Surface.Ty -> Option (List Core.Ty) :=
  List.mapM (·.translate G Δ)
