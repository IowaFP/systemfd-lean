import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

-- notation t1 ";;" t2 => t1 (t2)
-- notation t1 "::" t2 => Term.cons t1 t2

def NatCtx : Ctx Term := [
    .ctor (#1 -t> #1),
    .ctor #0,
    .datatype ★
  ]

def ex_pred : Term := `λ[#2]
  .ite #2 #0 #0
  (.ite #1 #0 (`λ[#3] #0) #0)

def ex_succ : Term := #0


#eval infer_type NatCtx ex_pred
#eval infer_type NatCtx ex_succ
#eval! infer_type NatCtx (ex_pred `@ (ex_succ `@ #1))


#eval! eval_ctx_loop NatCtx [ex_pred `@ (ex_succ `@ #1)]

#eval! eval_ctx_loop NatCtx [ex_pred `@ (ex_succ `@ (ex_succ `@ #1))]
