import Surface.Global
import Core.Global

import Surface.Typing

import Translation.Ty

def Core.is_valid_ctor_ty (G : Core.GlobalEnv) : Core.Ty -> Option String
| .all _ T => is_valid_ctor_ty G T
| .arrow _ T => is_valid_ctor_ty G T
| t => do let (x, _) <- t.spine
          if Core.is_data G x then return x else none


def Surface.is_valid_ctor_ty (G : Surface.GlobalEnv) : Surface.Ty -> Option String
| .all _ T => is_valid_ctor_ty G T
| .arrow _ T => is_valid_ctor_ty G T
| t => do let (x, _) <- t.spine
          if Surface.is_data G x then return x else none


def Surface.Ty.translate_ctors (G : Core.GlobalEnv) (ctors : Vect n  (String × Surface.Ty)) : Option (Vect n (String × Core.Ty)) := do
  -- check that names are unique
  let cns : Vect n String := (λ x => x.1) <$> ctors

  let octors : Vect n (Option (String × Core.Ty)) :=  (λ (x, ty) =>
    do let ty' := ty.translate
       let _ <- Core.is_valid_ctor_ty G ty'
       return (x , ty')) <$> ctors
  octors.seq



@[simp]
def Surface.Global.translate (G : Core.GlobalEnv) : Global -> Option Core.Global
| .data (n := n) x K ctors => do
  let ctors' <- Ty.translate_ctors ((Core.Global.data 0 x K.translate Vect.nil) :: G) ctors
  return Core.Global.data n x K.translate ctors'

@[simp]
def Surface.GlobalEnv.translate : Surface.GlobalEnv -> Option (Core.GlobalEnv)
| [] => return []
| .cons g gs => do
  let gs' <- Surface.GlobalEnv.translate gs
  let g' <- g.translate gs'
  return g' :: gs'


namespace Test.Core.Global


#guard (gt`#"One").translate == gt#"One"

end Test.Core.Global
