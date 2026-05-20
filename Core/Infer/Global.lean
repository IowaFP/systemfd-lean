import Core.Infer.Kind
import Core.Infer.Type

import Lilac
open Lilac

namespace Core

@[simp]
def GlobalEnv.wf_globals : GlobalEnv -> Option Unit
| .nil => return ()
| .cons (.data (n := n) x k ctors) G => do
  wf_globals G
  -- let ctors' : Fun.Vec (Option Kind) n := λ i => (ctors.get_elem i).snd.infer_kind ((.data _ x k Vec.nil) :: G) []
 -- let _ <- ctors'.to.seq
-- | .cons (.opent _ _) G => do
--   wf_globals G
| .cons (.openm x spTy) G => do
  wf_globals G
  if (lookup x G).isNone
  then spine_kinding G spTy
  else none
| .cons (.octor x spTy) G => do
  wf_globals G
  if (lookup x G).isNone
  then spine_kinding G spTy
  else none
| .cons (.defn x T t) G => do
  wf_globals G
  let T' <- t.infer_type G [] []
  let _ <- T.infer_kind G []
  if T == T' && (lookup x G).isNone then return () else none
| .cons (.inst x _ t) G => do
  wf_globals G
  let e := lookup x G
  match e with
  | some (.openm _ ⟨_, Ks, _, Ts, R⟩) => do
    let T <- t.infer_type G Ks.to_list Ts.to_list
    if T == R then return () else none
  | _ => none

| .cons (.odata x _) G => do
  wf_globals G
  if (lookup x G).isNone
  then return () else none
end Core
