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
  if (lookup x G).isNone then
  let mctors' : Fun.Vec (Option Unit) n := λ i => spine_kinding (.data (n := 0) x k .nil :: G) (ctors.get_elem i).snd
  let _ <- mctors'.to.seq
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
| .cons (.inst  x p t) G => do
  wf_globals G
  let e := lookup x G
  match e with
  | some (.openm _ ⟨_, Ks, m, Ts, R⟩) => do
      let Γ <- pattern_binders G Ks.to_list m Ts p
      let T <- t.infer_type G Ks.to_list Γ
      if T == R then return () else none
  | _ => none

| .cons (.odata x _) G => do
  wf_globals G
  if (lookup x G).isNone
  then return () else none
end Core
