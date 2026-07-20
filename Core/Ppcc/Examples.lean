import Core.Examples.Boolean
import Core.Ppcc.Basic
import Core.Eval

namespace Core.EqGraph.Test

def CtxWf : ⊢ [] := by constructor

def mEG : Option (Core.Ppcc.EqGraph [] [★, ★, ★, ★] [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])
  := Core.Ppcc.EqGraph.process_tyenv (G := []) (Δ := [★, ★, ★, ★]) (wf := CtxWf) (Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])

def test : Option Term := do
  let eG <- mEG
  let ⟨t, _⟩ <- eG.ask (G := []) (Δ := [★, ★, ★, ★]) (wf := CtxWf) (Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2]) ★ t#1 t#1
  return t

#eval! test

end Core.EqGraph.Test
