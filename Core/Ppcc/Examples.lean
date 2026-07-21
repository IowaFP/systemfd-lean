import Core.Examples.Boolean
import Core.Ppcc.Basic
import Core.Eval

import Core.Infer

namespace Core.EqGraph.Test

def CtxWf : ⊢ [] := by constructor

def mEG1 : Option (Core.Ppcc.EqGraph [] [★, ★, ★, ★] [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])
  := Core.Ppcc.EqGraph.process_tyenv (G := []) (Δ := [★, ★, ★, ★]) (wf := CtxWf) (Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])

def test1 : Option Ty := do
  let eG <- mEG1
  let Δ := [★, ★, ★, ★]
  let Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ  ★ t#1 t#2
  Term.infer_type [] Δ Γ t

#guard test1 == some (t#1 ~[★]~ t#2)

def mEG2 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)])
  := Core.Ppcc.EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)]

def test2 : Option Ty := do
  let eG <- mEG2
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★]
  let Γ := [(t#0 • t#2) ~[★]~ (t#1 • t#3)]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ (★ -:> ★) t#0 t#1
  Term.infer_type [] Δ Γ t

#guard test2 == some (t#0 ~[★ -:> ★]~ t#1)

end Core.EqGraph.Test
