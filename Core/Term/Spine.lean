import LeanSubst
import Core.Term.Definition

open LeanSubst

inductive SpineElem : Type where
| type (x : Ty)
| term (x : Term)

def Term.spine : Term -> Option (String × List SpineElem)
| g#x => return (x, [])
| ctor2 .app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [.term a])
| f •[a] => do
  let (x, sp) <- spine f
  (x, sp ++ [.type a])
| _ => none
