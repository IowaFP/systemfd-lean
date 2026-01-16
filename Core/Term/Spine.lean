import LeanSubst
import Core.Term.Definition
import Core.Term.Beq

open LeanSubst

inductive SpineElem : Type where
| type (x : Ty)
| term (x : Term)
| oterm (x : Term)

def SpineElem.beq : SpineElem -> SpineElem -> Bool
| type A, type B => A == B
| term a, term b => a == b
| oterm a, oterm b => a == b
| _, _ => false

instance : BEq SpineElem where
  beq := SpineElem.beq

def Term.spine : Term -> Option (String × List SpineElem)
| g#x => return (x, [])
| ctor2 .app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [.term a])
| f ∘[a] => do
  let (x, sp) <- spine f
  (x, sp ++ [.oterm a])
| f •[a] => do
  let (x, sp) <- spine f
  (x, sp ++ [.type a])
| _ => none

def Term.apply (t : Term) : List SpineElem -> Term
| [] => t
| .cons (.type A) tl => (t •[A]).apply tl
| .cons (.term a) tl => (t • a).apply tl
| .cons (.oterm a) tl => (t ∘[a]).apply tl

@[simp]
def Spine.prefix_equal [BEq T] : List T -> List T -> Option (List T)
| [], t => .some t
| .cons _ _, [] => .none
| .cons x1 t1, .cons x2 t2 => if x1 == x2 then prefix_equal t1 t2 else .none
