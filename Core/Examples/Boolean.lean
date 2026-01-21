import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep


/- data Bool = True | False -/
def BoolCtx : List Global := [
  .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]
  ]

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
         v[
         g# "False",
         g# "True" ]

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
  match! #1 v[ "True", "False" ]
   v[ match! #0 v[ "True", "False" ] v[ g#"True", g#"False"] ,
      match! #0 v[ "True", "False" ] v[ g# "False", g# "False"]
    ]


def EqBoolCtx : List Global := [
  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. ==@Bool ▹ sym c
  .inst "eq" (Λ[ ★ ] λ[ .open, gt#"Eq" • t#0 ]
        .guard (g#"EqBool" •[ t#0 ]) #0
           (λ[.open, t#1 ~[★]~ gt#"Bool"] (g#"eqBool" ▹ sym! (#0 -c> #0 -c> refl! gt#"Bool")))
   ),

  .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool,

  -- EqBool : ∀ t. t ~ Bool → Eq t
  .instty "EqBool" (∀[★] (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)) ,

  -- == : ∀ t. Eq t → t → t → Bool
  .openm "eq" (∀[★] (gt#"Eq" • t#0) -:> t#0 -:> t#0 -:> gt#"Bool") ,

  -- class Eq a
  .opent "Eq" (★ -:> ◯)
  ] ++ BoolCtx

def t1 : Term := (g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True") • g#"False"
def t2 : Term := (g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True") • g#"True"

#eval! eval_loop EqBoolCtx t1
#eval! eval_loop EqBoolCtx t2

#eval! eval EqBoolCtx t1
def t3 := Option.getD (eval EqBoolCtx t1) `0
#eval! eval EqBoolCtx t3
def t4 := Option.getD (eval EqBoolCtx t3) `0
#eval! eval EqBoolCtx t4
def t5 := Option.getD (eval EqBoolCtx t4) `0
#eval! eval EqBoolCtx t5
def t6 := Option.getD (eval EqBoolCtx t5) `0
#eval! eval EqBoolCtx t6
def t7 := Option.getD (eval EqBoolCtx t6) `0
#eval! eval EqBoolCtx t7
def t8 := Option.getD (eval EqBoolCtx t7) `0
#eval! eval EqBoolCtx t8
def t9 := Option.getD (eval EqBoolCtx t8) `0
#eval! eval EqBoolCtx t9
def t10 := Option.getD (eval EqBoolCtx t9) `0
#eval! eval EqBoolCtx t10
def t11 := Option.getD (eval EqBoolCtx t10) `0
#eval! eval EqBoolCtx t11
def t12 := Option.getD (eval EqBoolCtx t11) `0
#eval! eval EqBoolCtx t12
def t13 := Option.getD (eval EqBoolCtx t12) `0
#eval! eval EqBoolCtx t13
def t14 := Option.getD (eval EqBoolCtx t13) `0
#eval! eval EqBoolCtx t14
def t15 := Option.getD (eval EqBoolCtx t14) `0
#eval! eval EqBoolCtx t15
