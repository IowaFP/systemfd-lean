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
| _ -:> B => B.arity + 1
| ∀[_] P => P.arity + 1
| _ => 0
