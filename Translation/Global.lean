import Surface.Global
import Core.Global

import Translation.Ty

@[simp]
def Surface.Global.translate (gs : List Core.Global) : Global -> Option Core.Global
| .data (n := n) x K ctors => do
  let K' := K.translate
  let octors' : Vec (Option (String × Core.Ty)) n :=  λ i =>
    do let ty' : Core.Ty <- (ctors i).2.translate ((Core.Global.data x K' v[]) :: gs) []
       return ((ctors i).1 , ty')
  let ctors' <- octors'.seq
  return Core.Global.data x K' ctors'

@[simp]
def Surface.Global.translateEnv : Surface.GlobalEnv -> Option (List Core.Global)
| [] => return []
| .cons g gs => do
  let gs' <- translateEnv gs
  let g' <- g.translate gs'
  return g' :: gs'
