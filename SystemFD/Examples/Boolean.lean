
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def boolCtx : Ctx Term := [
    .ctor #1 -- True : Bool
  , .ctor #0 -- False : Bool
  , .datatype  ★   -- Bool : ★
]

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/
def notTerm : Term :=
       (`λ[ #2 ] Term.ite
                  #2 -- False
                  #0 -- x
                  #1 -- True
                  (Term.ite
                    #1
                    #0
                    #2
                    #2 -- False catch all
                  ))
/-      eqBool = λ x. λ y. case x of
                            True → case y of
                                    True → True
                                    False → False
                            False → case y of
                                    True → False
                                    False → True
 -/
def eqBoolTerm : Term :=
     `λ[#2] `λ[#3]
        (Term.ite #2 #1 (Term.ite #2 #0 #2 #3)
        (Term.ite #3 #1 (Term.ite #3 #0 #2 #3)
          #3))

#eval eqBoolTerm
#eval notTerm
-- not : Bool => Bool
#eval infer_type boolCtx notTerm
#eval eval_ctx_loop boolCtx (notTerm `@ #1)
#eval eval_ctx_loop boolCtx (notTerm `@ #0)

#eval infer_type boolCtx eqBoolTerm
#eval eval_ctx_loop boolCtx (eqBoolTerm `@ #1 `@ #1)
#eval eval_ctx_loop boolCtx (eqBoolTerm `@ #0 `@ #1)
