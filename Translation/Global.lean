import Surface.Global
import Core.Global

import Surface.Typing

import Translation.Ty


def Surface.Ty.translate_ctors (ctors : Vect n (String × Surface.Ty)) : (Vect n (String × Core.Ty)) :=
  (λ (x, ty) => (x , ty.translate)) <$> ctors


@[simp]
def Surface.Global.translate : Global -> Core.Global
| .data (n := n) x K ctors =>
  let ctors' := Ty.translate_ctors ctors
  -- Core.Ty.check_ctor_tys x (.data 0 x K.translate Vect.nil :: G) ctors'
  Core.Global.data n x K.translate ctors'

@[simp]
def Surface.GlobalEnv.translate : Surface.GlobalEnv -> Core.GlobalEnv
| [] => []
| .cons g gs => do
  let gs' := Surface.GlobalEnv.translate gs
  let g' := g.translate
  g' :: gs'

-- def Surface.Entry.translate : Surface.Entry -> Option


namespace Test.Core.Global


#guard (gt`#"One").translate == gt#"One"

end Test.Core.Global
