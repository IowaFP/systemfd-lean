import Hs.HsTerm
import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

def FDCtx : HsCtx HsTerm := [
  -- f : ∀ α. F Bool α ⇒ α → α → α = g
  .term (`∀{`★} `#12 `•k `#6 `•k `#0 ⇒ `#1 → `#2 → `#3) (Λ̈[`★]λ̈[`#12 `•k `#6 `•k `#0] `#2),
  -- g : Bool → Bool → Bool = λ x y. True
  .term (`#4 → `#5 → `#6) (λ̈[`#4]λ̈[`#5]`#5),
  -- F Bool Bool
  .inst (`#8 `•k `#2 `•k `#2)  .nil,
   -- data Bool = True | False
  .datatypeDecl `★ [`#0, `#1],
  -- data Tri = Yes | No | Perhaps
  .datatypeDecl `★ [`#0, `#1, `#2],
  -- class F t u | t ~> u
  .classDecl (`★ `-k> `★ `-k> `★) .nil [([1],0)] .nil
  ]

#eval DsM.run (compile_ctx FDCtx)
#guard (do
  let Γ' <- compile_ctx FDCtx
  .toDsMq (wf_ctx Γ')) == .ok ()
