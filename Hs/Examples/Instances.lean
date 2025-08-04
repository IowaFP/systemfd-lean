import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term

def ΓInsts : HsCtx HsTerm := [
  .inst (`#0 `•k `#3) .nil,
  .classDecl (`★ `-k> `★) .nil .nil .nil,
  .datatypeDecl `★ [`#0, `#1]
  ]

-- #eval! DsM.run (compile_ctx ΓInsts)
#guard (
  do let ctx <- compile_ctx ΓInsts
     .toDsMq (wf_ctx ctx)) == .ok ()

def ΓInsts' : HsCtx HsTerm := [
  .inst (`#1 `•k `#4) .nil, -- this should fail
  .inst (`#0 `•k `#3) .nil,
  .classDecl (`★ `-k> `★) .nil .nil .nil,
  .datatypeDecl `★ [`#0, `#1]
  ]

#eval! DsM.run (compile_ctx ΓInsts')  -- this should fail
