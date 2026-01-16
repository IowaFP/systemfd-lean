import LeanSubst

import Core.Vec
import Core.Ty
import Core.Term
import Core.Eval.SmallStep

open LeanSubst

partial def eval_loop (G : List Global) (t : Term) : Term :=
  match eval G t with
  | .none => t
  | .some t => eval_loop G t
