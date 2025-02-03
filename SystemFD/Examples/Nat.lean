import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

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

#eval infer_type NatCtx ex_pred
