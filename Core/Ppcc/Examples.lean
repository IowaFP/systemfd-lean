import Core.Examples.Boolean
import Core.Ppcc.Basic
import Core.Eval

import Core.Infer


namespace Core.Ppcc.Examples

#eval! do
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★]
  let Γ := [(t#0 • t#2) ~[★]~ (t#1 • t#3)]
  let eG : EqGraph [] Δ Γ := EqGraph.empty
  let eG <- eG.push_ty (t#0 • t#2)
  eG.push_ty (t#1 • t#3)



end Core.Ppcc.Examples
