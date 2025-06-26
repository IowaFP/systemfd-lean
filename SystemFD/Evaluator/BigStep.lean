import SystemFD.Evaluator.SmallStep
import SystemFD.Ctx

-- multistep evaluator
partial def eval_ctx_loop (Γ : Ctx Term) (t : Term) : Term :=
  match (eval_small_step Γ t) with
  | .none => t
  | .some t => eval_ctx_loop Γ t

partial def eval (t : Term) : Term := eval_ctx_loop [] t
