import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global

namespace Surface.Examples.FunDeps


def FunDepsCtx : GlobalEnv := [
  .classDecl "Equal" #(★, ★) [] [⟨"fdBwk", 0, #(0), 1⟩, ⟨"fdFwd", 0, #(1), 0⟩] []
  ]


#eval FunDepsCtx
#eval Translation.translate_SI FunDepsCtx
#eval! do
  let benv' <- Translation.translate_SI FunDepsCtx
  Translation.translate_IC benv'

end Surface.Examples.FunDeps
