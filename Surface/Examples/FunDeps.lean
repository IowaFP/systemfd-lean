
import Surface.Global
import Surface.Term

import Translation.Global

namespace Surface.Examples.FunDeps


def FunDepsCtx : GlobalEnv := [
  .instDecl "EqualTT" ⟨2, #(★, ★), 1, #(★), 2, #(t#2 ~[★]~ t#0, t#1 ~[★]~ t#0), (gt#"Equal" • t#2) • t#1⟩ [],

  .classDecl "Equal" #(★, ★) [⟨"fdBwk", [0], 1⟩, ⟨"fdFwd", [1], 0⟩] [] []

  ]


#eval FunDepsCtx
#eval Translation.translate_SI FunDepsCtx
-- #eval! do
--   let benv' <- Translation.translate_SI FunDepsCtx
--   Translation.translate_IC benv'

end Surface.Examples.FunDeps
