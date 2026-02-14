
import Lilac

namespace Vect
  def ex0 : Vect 0 Nat := .nil
  def ex1 : Vect 3 Nat := 1::2::3::.nil
  def ex2 : Vect 3 Nat := 1::2::[3]
  def ex3 : Vect 3 Nat := [1, 2, 3]
  def ex4 : Vect 3 Bool := (· < 2) <$> ex3

  inductive Ex where
  | base : Ex
  | stuff : Vect n Ex -> Ex

  def Ex.size : Ex -> Nat
  | base => 0
  | stuff vs =>
    let sizes : Vect _ _ := size <$> vs
    List.sum sizes + 1
end Vect

def main : IO Unit := do
  println! "Hello, World!"
