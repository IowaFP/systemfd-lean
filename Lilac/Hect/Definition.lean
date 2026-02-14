
import Lilac.Vect.Definition

def Hect (n : Nat) (A : Vect n (Sort u)) := (i : Fin n) -> A i

def Hect.nil : Hect 0 A := λ x => nomatch x

def Hect.cons (head : A) (tail : Hect n T) : Hect (n + 1) (A::T) :=
  Fin.cases (motive := A::T) head tail

infixr:67 (name := hect_cons) " ::: " => Hect.cons
