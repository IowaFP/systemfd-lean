
import Lilac.Vec.Encoding

namespace Lilac

inductive Vec (A : Sort u) : Nat -> Sort (imax u 1) where
| nil : Vec A 0
| cons : A -> Vec A n -> Vec A (n + 1)

notation "#𝓋[]" => Vec.nil
infixr:67 (name := vec_cons) " :: " => Vec.cons

-- Syntax adapted from Lean Prelude
----------------------------------------------------------------------------------------------------

syntax (name := «term#𝓋[_,]») "#𝓋[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#𝓋[ $elems,* ]) => do
    -- NOTE: we do not have `TSepArray.getElems` yet at this point
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(Vec.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expandListLit size (size % 2 == 0) (← ``(Vec.nil))
    else
      `(%[ $elems,* | Vec.nil ])

@[app_unexpander Vec.nil]
meta def Vec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(#𝓋[])

@[app_unexpander Vec.cons]
meta def Vec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `([])      => `(#𝓋[$x])
  | `([$xs,*]) => `(#𝓋[$x, $xs,*])
  | `(⋯)       => `(#𝓋[$x, $tail])
  | _          => throw ()
| _ => throw ()

----------------------------------------------------------------------------------------------------

@[coe]
def Fun.Vec.to (v : Lilac.Fun.Vec A n) : Lilac.Vec A n :=
  @induction A (λ n _ => Lilac.Vec A n) Lilac.Vec.nil (λ hd _ tl => Lilac.Vec.cons hd tl) _ v

@[simp]
theorem Fun.Vec.to_nil : to (nil : Vec A 0) = .nil := by rfl

@[simp]
theorem Fun.Vec.to_cons : to (cons hd tl) = .cons hd tl.to := by rfl

@[simp]
instance : Coe (Lilac.Fun.Vec A n) (Lilac.Vec A n) where
  coe := Fun.Vec.to

@[simp]
def Vec.to : Vec A n -> Fun.Vec A n
| nil => .nil
| cons hd tl => .cons hd tl.to

end Lilac
