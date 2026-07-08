import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Kind
import Core.Typing

import Core.Examples.Common
import Core.Examples.Boolean

open LeanSubst

namespace Core.Examples.ClassAlias

def CACtx : GlobalEnv := [
  .openm "mpRequirement" ⟨1, #(★ -:> ★), 0, #(), 2, #(gt#"Monad" • t#0, gt#"Alternative" • t#0), gt#"MonadPlus" • t#0⟩,
  -- class MonadPlus (m : ★ → ★)
  .odata "MonadPlus" ((★ -:> ★) -:> ★),
  -- class Alternative (m : ★ → ★)
  .odata "Alternative" ((★ -:> ★) -:> ★),
  -- class Monad (m : ★ → ★)
  .odata "Monad" ((★ -:> ★) -:> ★) ]

#guard CACtx.wf_globals == some ()
#guard CACtx.check_open_exhaustive == some ()

end Core.Examples.ClassAlias
