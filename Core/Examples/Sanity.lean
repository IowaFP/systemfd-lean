import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Algorithm.Kind

/- data Bool = True | False -/
def BoolCtx : List Global := [
  .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]
  ]
#guard infer_kind BoolCtx [] (gt#"Bool") == .some ★
#guard infer_kind BoolCtx [] (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") == .some ★
/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/
def notTerm : Term := λ[ .closed , .global "Bool" ]
  match! #0
         v[ "True", "False" ]
         v[ g# "False", g# "True" ]

/-  eqBool =
  λ x. λ y. case x of
              True → case y of
                       True → True
                       False → False
              False → case y of
                       True → False
                       False → True
 -/
def eqBool : Term := λ[ .closed,  .global "Bool" ] λ[ .closed, .global "Bool" ]
  match!  #1
   v[ "True", "False" ]
   v[ match! #0 v[ "True", "False" ] v[ g#"True", g#"False" ] ,
      match! #0 v[ "True", "False" ] v[ g# "False", g# "False"]
    ]

def EqBoolCtx := [.defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool] ++ BoolCtx

def t1 := Term.match g#"False"
              v[ "True", "False" ] v[ g#"False" , g#"True" ]

def t2 := Term.match g#"True"
              v[ "True", "False" ]  v[ g#"True" , g#"False" ]


-- #eval ctor_idx "True" EqBoolCtx
-- #eval Fin.ofNat 2 0


-- #eval ctor_idx "False" EqBoolCtx
-- #eval Fin.ofNat 2 1


#eval v[ g#"True", g#"False"] 0 -- g#"True"

#eval v[ g#"True", g#"False"] 1 -- g#"False"

#guard eval EqBoolCtx t1 == g#"True"
#guard eval EqBoolCtx t2 == g#"True"
