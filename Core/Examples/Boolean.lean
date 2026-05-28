import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Type
import Core.Infer.Global
import Lilac
open Lilac

namespace Core.Examples

/- data Bool = True | False -/
def BoolCtx : List Global := [
  Global.data 2 "Bool" ★
             #𝓋[ ("True", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)
               , ("False", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)]
  ]

def TrueCtor := ctor! "True" #𝓋[] .nil
def FalseCtor := ctor! "False" #𝓋[] .nil

#guard TrueCtor.infer_type BoolCtx [] [] == .some gt#"Bool"
#guard GlobalEnv.wf_globals [] == some ()

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
-/
def notTerm : Core.Term := λ[  gt#"Bool" ]
  mtch' #𝓋[#0]
     #𝓋[ (#𝓋[⟨"True", 0,  #𝓋[] , 0⟩] , TrueCtor)
       , (#𝓋[⟨"False", 0 , #𝓋[] , 0⟩] , FalseCtor) ]

#guard Term.infer_type BoolCtx [] [] notTerm == some (gt#"Bool" -:> gt#"Bool")

/-  eqBool =
  λ x. λ y. case x of
              True → case y of
                       True → True
                       False → False
              False → case y of
                       True → False
                       False → True
 -/
def eqBool : Term := λ[ gt#"Bool" ] λ[ gt#"Bool" ]
  (mtch' #𝓋[#1]
     #𝓋[ (#𝓋[⟨"True", 0 , #𝓋[] , 0⟩]  ,
          (mtch' #𝓋[#0]
                 #𝓋[ (#𝓋[ ⟨"True", 0 , #𝓋[] , 0⟩ ], TrueCtor)
                   , (#𝓋[ ⟨"False", 0 , #𝓋[] , 0⟩ ] , FalseCtor)
                   ]))

       , (#𝓋[⟨"False", 0 , #𝓋[] , 0⟩]  ,
          (mtch' #𝓋[#0]
                 #𝓋[ (#𝓋[ ⟨"True", 0 , #𝓋[] , 0⟩ ], FalseCtor)
                   , (#𝓋[ ⟨"False", 0 , #𝓋[] , 0⟩ ] , TrueCtor)
                   ]))])

#guard Term.infer_type BoolCtx [] [] eqBool == some (gt#"Bool" -:> (gt#"Bool" -:> gt#"Bool"))


def EqBoolCtx : GlobalEnv := [
  -- instance (==)[t] i
  --    If EqBool[t] t~Bool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. ==@Bool ▹ sym c
  .inst "eq" #𝓋[⟨"EqBool", 1, #𝓋[t#0], 1⟩] (λ[ t#0 ] λ[ t#0 ] -- #2 t ~ Bool
        (((d#"eqBool" • (.cast t#0 #2 #1)) • (.cast t#0 #2 #0))) ),

  -- .defn "test" (∀[★] λ [t#0 ~[★]~ gt#"Bool"] λ[ t#0 ] λ[ t#0 ])

  -- ==@Bool
  .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool,

  -- EqBool : ∀ t. t ~ Bool → Eq t
  .octor "EqBool" ⟨1, #𝓋[★], 1 , #𝓋[t#0 ~[★]~ gt#"Bool"], (gt#"Eq" • t#0)⟩ ,

  -- == : ∀ t. Eq t → t → t → Bool
  .openm "eq" ⟨1, #𝓋[★], 1, #𝓋[gt#"Eq" • t#0], t#0 -:> t#0 -:> gt#"Bool"⟩ ,

  -- class Eq a
  .odata "Eq" (★ -:> ★),

  ] ++ BoolCtx


-- def t1 : Term := (d#"eq" •[ gt#"Bool" ]  • (gt#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True") • g#"False"
-- def t2 : Term := (g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True") • g#"True"


-- def ctx' := List.drop 1 EqBoolCtx
-- #eval! (Λ[★] λ[(t#0 ~[★]~ gt#"Bool")] λ[t#0] λ[t#0]
--              (((d#"eqBool" • (.cast t#0 #2 #1)) • (.cast t#0 #2 #0)))).infer_type EqBoolCtx [] []

#guard EqBoolCtx.wf_globals  == some ()
#eval ((d#"eqBool" • TrueCtor) • TrueCtor).eval_loop EqBoolCtx
#eval ((d#"eqBool" • TrueCtor) • FalseCtor).eval_loop EqBoolCtx

-- #guard t2.eval_loop EqBoolCtx == g#"True"

-- -- #eval! eval EqBoolCtx t1
-- -- def t3 := Option.getD (eval EqBoolCtx t1) `0
-- -- #eval! eval EqBoolCtx t3
-- -- def t4 := Option.getD (eval EqBoolCtx t3) `0
-- -- #eval! eval EqBoolCtx t4
-- -- def t5 := Option.getD (eval EqBoolCtx t4) `0
-- -- #eval! eval EqBoolCtx t5
-- -- def t6 := Option.getD (eval EqBoolCtx t5) `0
-- -- #eval! eval EqBoolCtx t6
-- -- def t7 := Option.getD (eval EqBoolCtx t6) `0
-- -- #eval! eval EqBoolCtx t7
-- -- def t8 := Option.getD (eval EqBoolCtx t7) `0
-- -- #eval! eval EqBoolCtx t8
-- -- def t9 := Option.getD (eval EqBoolCtx t8) `0
-- -- #eval! eval EqBoolCtx t9
-- -- def t10 := Option.getD (eval EqBoolCtx t9) `0
-- -- #eval! eval EqBoolCtx t10
-- -- def t11 := Option.getD (eval EqBoolCtx t10) `0
-- -- #eval! eval EqBoolCtx t11
-- -- def t12 := Option.getD (eval EqBoolCtx t11) `0
-- -- #eval! eval EqBoolCtx t12
-- -- def t13 := Option.getD (eval EqBoolCtx t12) `0
-- -- #eval! eval EqBoolCtx t13
-- -- def t14 := Option.getD (eval EqBoolCtx t13) `0
-- -- #eval! eval EqBoolCtx t14
-- -- def t15 := Option.getD (eval EqBoolCtx t14) `0
-- -- #eval! eval EqBoolCtx t15
-- -- def t16 := Option.getD (eval EqBoolCtx t15) `0
-- -- #eval! eval EqBoolCtx t16
-- -- def t17 := Option.getD (eval EqBoolCtx t16) `0
-- -- #eval! eval EqBoolCtx t17

end Core.Examples
