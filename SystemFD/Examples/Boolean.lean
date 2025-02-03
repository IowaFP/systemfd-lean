
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

def boolCtx : Ctx Term := [
    .ctor #1 -- True : Bool
  , .ctor #0 -- False : Bool
  , .datatype  ★   -- Bool : ★
]

  -- not : Bool -> Bool
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
                  )

       )


def eqBoolTerm : Term :=
     `λ[#2] `λ[#2]
        (Term.ite #2 #1 (Term.ite #2 #0 #2 #3)
        (Term.ite #3 #1 (Term.ite #3 #0 #2 #3)
          #13))
