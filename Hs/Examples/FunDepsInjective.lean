import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term

def FDCtx' : HsCtx HsTerm := [
  -- ∀ a b F a b => F (Maybe a) (Maybe b)
  .inst (`∀{`★}`∀{`★} (`#13 `•k `#1 `•k `#0) ⇒ `#14 `•k (`#11 `•k `#2) `•k (`#11 `•k `#1))  .nil,

  -- F Int Bool
  .inst (`#8 `•k `#9 `•k `#2) .nil,

  -- data Bool = True | False
  .datatypeDecl `★ [`#0, `#1],
  -- data Maybe a = Nothing | Just a
  .datatypeDecl (`★ `-k> `★) [ `∀{`★} (`#1 `•k `#0),  `∀{`★} `#0 → `#3 `•k `#1],
  -- F a b | a ~> b, b ~> a
  .classDecl (`★ `-k> `★ `-k> `★) -- F t u
    .nil [([1],0), ([0], 1)] --- t ~> u, u ~> t
    .nil,
  .datatypeDecl `★ .nil -- data Int
]

#eval DsM.run (compile_ctx FDCtx')
#guard (do
  let Γ' <- compile_ctx FDCtx'
  .toDsMq (wf_ctx Γ')) == .ok ()
