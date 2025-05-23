import SystemFD.Evaluator.SmallStep
import SystemFD.Ctx

-- Goes over the list of terms and evaluates each of them by one step
-- @[simp]
-- def eval_outer (Γ : Ctx Term) (ts : Term) : Option Term :=
--   match ts with
--   | `0 => .some `0
--   | .choice t ts => do
--     let t' <- eval_inst Γ t
--     let ts' <- eval_outer Γ ts
--     .some (t' ++ ts')

-- multistep evaluator
unsafe def eval_ctx_loop (Γ : Ctx Term) (t : Term) : Term :=
  match (eval_inst Γ t) with
  | .none => t
  | .some t => eval_ctx_loop Γ t

unsafe def eval (t : Term) : Term := eval_ctx_loop [] t
