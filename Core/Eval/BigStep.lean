import LeanSubst

import Core.Vec
import Core.Ty
import Core.Term
import Core.Eval.SmallStep

open LeanSubst

namespace Core

partial def Term.eval_loop (G : List Global) (t : Term) : Term :=
  match eval G t with
  | .none => t
  | .some t => Term.eval_loop G t

end Core
