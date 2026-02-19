import Core.Infer.Kind
import Core.Infer.Type

namespace Core

@[simp]
def Globals.wf_globals : (G : GlobalEnv) -> Option Unit
| .nil => return ()
| .cons (.data (n := n) x k ctors) tl => do
  wf_globals tl
  let ctors' : Vec (Option Kind) n := λ i => (ctors i).snd.infer_kind ((.data x k v[]) :: tl) []
  let _ <- ctors'.seq
| .cons (.opent _ _) tl => do
  wf_globals tl
| .cons (.openm _ T) tl => do
  wf_globals tl
  let _ <- T.infer_kind tl []
| .cons (.defn _ T t) tl => do
  wf_globals tl
  let T' <- t.infer_type tl [] []
  let _ <- T.infer_kind tl []
  if T == T' then return () else none
| .cons (.inst x t) tl => do
  wf_globals tl
  let T <- t.infer_type tl [] []
  let T' <- lookup_type tl x
  if T == T' then return () else none
| .cons (.instty _ T) tl => do
  wf_globals tl
  let _ <- T.infer_kind tl []

end Core
