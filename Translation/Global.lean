import Surface.Global
import Core.Global

import Surface.Typing

import Translation.Ty
import Translation.Term






def Surface.Ty.translate_ctors (ctors : Vect n (String × Surface.Ty)) : (Vect n (String × Core.Ty)) :=
  (λ (x, ty) => (x , ty.translate)) <$> ctors


-- @[simp]
-- def Surface.Global.translate (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) : Global -> Option Core.Global
-- | .data (n := n) x K ctors =>
--   let ctors' := Ty.translate_ctors ctors
--   Core.Global.data n x K.translate ctors'
-- | instDecl x t => do
--   let T <- Surface.lookup_type G x
--   let t' <- t.type_chk_translate G G' [] [] T
--   return .inst x t'
-- | defn x T t => do
--   let t' <- t.type_chk_translate G G' [] [] T
--   return .defn x T.translate t'
-- | openm x T => return .openm x T.translate
-- | opent x K => return .opent x K.translate



-- @[simp]
-- def Surface.GlobalEnv.translate : Surface.GlobalEnv -> Option (Core.GlobalEnv)
-- | [] => return []
-- | .cons g gs => do
--   let gs' <- Surface.GlobalEnv.translate gs
--   let g' <- g.translate gs gs'
--   return (g' :: gs')

-- def Surface.Entry.translate : Surface.Entry -> Option

inductive Surface.Global.Elab : Surface.GlobalEnv -> Core.GlobalEnv -> Prop
| nil : Surface.Global.Elab [] []
| defn :
  Surface.Global.Elab G G' ->
  Surface.Term.Elab G G' .chk [] [] t T t' ->
  Surface.Global.Elab (.cons (.defn x T t) G) ((.defn x (T.translate) t') :: G')
| data {n : Nat} {ctors : Vect n (String × Ty)} {ctors' : Vect n (String × Core.Ty)} :
  Surface.Global.Elab G G' ->
  ctors' = (λ i => ((ctors i).1 , (ctors i).2.translate)) ->
  Surface.Global.Elab (.cons (.data (n := n) x K ctors) G) (.cons (.data n x K.translate ctors') G')

notation:170 G:170 " -↪ " G':170 => Surface.Global.Elab G G'

namespace Test.Core.Global

#guard (gt`#"One").translate == gt#"One"

end Test.Core.Global
