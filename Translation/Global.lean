import Surface.Global
import Core.Global

import Translation.Ty
import Translation.Term

def trans_global (gs : List Global) : Surface.Global -> Option Global
| .data (n := n) x K ctors => do
  let K' := trans_ki K
  let octors' : Vec (Option (String × Ty)) n :=  λ i =>
    do let ty' <- trans_ty ((Global.data x K' v[]) :: gs) [] (ctors i).2
       return ((ctors i).1 , ty')
  let ctors' <- octors'.seq
  return .data x K' ctors'


def trans_globals : List Surface.Global -> Option (List Global)
| [] => return []
| .cons g gs => do
  let gs' <- trans_globals gs
  let g' <- trans_global gs' g
  return g' :: gs'
