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
def notTerm : Term := λ[ .global "Bool" ]
  match! g# "True" #0 v[
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
def eqBool : Term := λ[ .global "Bool" ] λ[ .global "Bool" ]
  match! (g# "True") #1
   v[ match! (g# "True") #0 v[ g#"True", g#"False"] ,
      match! (g# "True") #0 v[ g# "False", g# "False"]
    ]


def EqBoolCtx : List Global := [
  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. ==@Bool ▹ sym c
  .inst "eq" (Λ[ ★ ] λ[ gt#"Eq" • t#0 ]
        .guard (g#"EqBool") #0
           (λ[t#1 ~[★]~ gt#"Bool"] g#"eqBool" ▹ sym! (#0 -c> #0 -c> refl! gt#"Bool"))
   ),

  .let "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool,

  -- EqBool : ∀ t. t ~ Bool → Eq t
  .instty "EqBool" (∀[★] (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)) ,

  -- == : ∀ t. Eq t → t → t → Bool
  .openm "eq" (∀[★] (gt#"Eq" • t#0) -:> t#0 -:> t#0 -:> gt#"Bool") ,

  -- class Eq a
  .opent "Eq" (★ -:> ◯)
  ] ++ BoolCtx

def t1 : Term := g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True" • g#"False"
def t2 : Term := g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True" • g#"True"


#eval! eval_loop EqBoolCtx t1
-- #eval! g#"eqBool" • g#"True" • g#"False"


/-
(((λ[ t#0~[★]~gt#Bool ] (g#eqBool • (sym! (#0 -c> (#0 -c> (refl! gt#Bool)))))) •[gt#Bool]) • (refl! gt#Bool)) • g#True • g#False

-/
