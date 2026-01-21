import LeanSubst
import Core.Ty.Definition

open LeanSubst

def Ty.spine : Ty -> Option (String × List Ty)
| gt#x => return (x, [])
| app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [a])
| _ => none

def Ty.arity : Ty -> Nat
| arrow _ _ B => B.arity + 1
| ∀[_] P => P.arity + 1
| _ => 0


inductive TyTeleElem
| kind (k  : Kind)
| ty (b : BaseKind) (t : Ty)

def TyTele  := List TyTeleElem

def Ty.split : Ty -> TyTele × Ty
| .arrow K A B =>
  let (tys, b) := B.split
  (.ty K A :: tys, b)
| .all K B =>
  let (tys, b) := B.split
  (.kind K :: tys, b)
| t => ([], t)

def Ty.mk_from_tele : TyTele -> Ty -> Ty
| .nil , t => t
| .cons (.ty K A) tys, t =>
  let r := t.mk_from_tele tys
  A -[K]> r
| .cons (.kind K) tys, t =>
  let r := t.mk_from_tele tys
  ∀[K] r
