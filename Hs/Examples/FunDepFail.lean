import Hs.HsTerm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

def FDCtx : HsCtx HsTerm := [
  -- F Tri Bool
  .inst (`#10 `•k `#4 `•k `#8) .nil, -- Fails with fundep violated
  -- F Tri Tri
  .inst (`#8 `•k `#2 `•k `#2) .nil,
  -- Bool
  .datatypeDecl `★ [`#0, `#1],
  -- Tri
  .datatypeDecl `★ [`#0, `#1, `#2],
  -- F t u | t ~> u
  .classDecl (`★ `-k> `★ `-k> `★)
    .nil [([1],0)] .nil
]

#eval DsM.run (compile_ctx FDCtx)
#eval DsM.run (do
  let Γ' <- compile_ctx FDCtx
  .toDsMq (wf_ctx Γ'))
