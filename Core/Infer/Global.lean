import Core.Infer.Kind
import Core.Infer.Type

import Lilac
open Lilac

namespace Core

@[simp]
def GlobalEnv.wf_globals : (G : GlobalEnv) -> Option Unit
| .nil => return ()
| .cons (.data (n := n) x k ctors) tl => do
  wf_globals tl
  -- let ctors' : Fun.Vec (Option Kind) n := λ i => (ctors.get_elem i).snd.infer_kind ((.data _ x k Vec.nil) :: tl) []
 -- let _ <- ctors'.to.seq
-- | .cons (.opent _ _) tl => do
--   wf_globals tl
| .cons (.openm _ spTy) tl => do
  wf_globals tl
  -- let _ <- spTy.mkTy.infer_kind tl []
| .cons (.octor _ spTy) tl => do
  wf_globals tl
  -- let _ <- spTy.mkTy.infer_kind tl []
| .cons (.defn _ T t) tl => do
  wf_globals tl
  let T' <- t.infer_type tl [] []
  let _ <- T.infer_kind tl []
  if T == T' then return () else none
| .cons (.inst x pat t) tl => do
  wf_globals tl
  -- let T <- t.infer_type tl [] []
  -- let T' <- lookup_type tl x
  -- if T == T' then return () else none
| .cons (.odata _ spTyT) tl => do
  wf_globals tl
  -- let _ <- T.infer_kind tl []
end Core
