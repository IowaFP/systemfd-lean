import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term

def FDCtx : HsCtx HsTerm := [
  -- f : ∀ α. F Int α ⇒ α → α = not
  .term (`∀{`★} `#12 `•k `#13 `•k `#0 ⇒ `#1 → `#2) (Λ̈[`★]λ̈[`#12 `•k `#13 `•k `#0] `#2),
  -- not : Bool → Bool = λ x. If true Then false Else True
  .term (`#4 → `#5) (λ̈[`#4] .HsIte (.HsAnnotate `#5 `#4) (.HsAnnotate `#5 `#0) (.HsAnnotate `#5 `#3) `#4),
  -- F Int Bool
  .inst (`#8 `•k `#9 `•k `#2)  .nil,
   -- data Bool = True | False
  .datatypeDecl `★ [`#0, `#1],
  -- data Tri = Yes | No | Perhaps
  .datatypeDecl `★ [`#0, `#1, `#2],
  -- class F t u | t ~> u
  .classDecl (`★ `-k> `★ `-k> `★) .nil [([1],0)] .nil,
  -- datatype Int
  .datatypeDecl `★ .nil
  ]

#eval DsM.run (compile_ctx FDCtx)
#guard (do
  let Γ' <- compile_ctx FDCtx
  .toDsMq (wf_ctx Γ')) == .ok ()
