
import Lilac

namespace Lilac.Example
  def ex0 : Fun.Vec Nat 0 := .nil
  def ex1 : Fun.Vec Nat 3 := #(1,2,3).to
  def ex2 : Fun.Vec Bool 3 := (· < 2) <$> ex1
  def ex3 : Vec Nat 0 := #()

  inductive Ex where
  | base : Ex
  | stuff : Fun.Vec Ex n -> Ex

  def Ex.size : Ex -> Nat
  | base => 0
  | stuff vs =>
    let sizes : Fun.Vec _ _ := size <$> vs
    Vec.sum sizes.to + 1
end Lilac.Example
