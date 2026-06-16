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
def BoolCtx : GlobalEnv := [
  Global.data 2 "Bool" ★
             #𝓋[ ("True", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)
               , ("False", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)]
  ]

def TrueCtor : Term := ctor! "True" #𝓋[] .nil
def FalseCtor : Term := ctor! "False" #𝓋[] .nil

#guard TrueCtor.infer_type BoolCtx [] [] == .some gt#"Bool"
#guard GlobalEnv.wf_globals [] == some ()
#guard GlobalEnv.wf_globals BoolCtx == some ()

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

#eval EqBoolCtx
#guard EqBoolCtx.wf_globals  == some ()

#eval lookup_octor EqBoolCtx (gt#"Eq")

#eval ((d#"eqBool" • TrueCtor) • TrueCtor).eval_loop EqBoolCtx
#eval ((d#"eqBool" • TrueCtor) • FalseCtor).eval_loop EqBoolCtx

def iBool : Term := inst! "EqBool" #𝓋[ gt#"Bool" ] (Vec.to #𝓋[ refl! gt#"Bool"])
#guard iBool.infer_type EqBoolCtx [] [] == some (gt#"Eq" • gt#"Bool")

-- #eval get_instance "EqBool" ((#𝓋[ iBool ])) EqBoolCtx

def t1 : Term := ((openm! "eq" #𝓋[ gt#"Bool" ] (Vec.to (#𝓋[ iBool ]))) • TrueCtor) • FalseCtor
#guard t1.infer_type EqBoolCtx [] [] == some (gt#"Bool")
-- def t2 : Term := (g#"eq" •[ gt#"Bool" ]  • (g#"EqBool" •[  gt#"Bool" ] • refl! gt#"Bool") • g#"True") • g#"True"

#eval t1.eval_loop EqBoolCtx

-- def ctx' := List.drop 1 EqBoolCtx
-- #eval! (Λ[★] λ[(t#0 ~[★]~ gt#"Bool")] λ[t#0] λ[t#0]
--              (((d#"eqBool" • (.cast t#0 #2 #1)) • (.cast t#0 #2 #0)))).infer_type EqBoolCtx [] []

def t2 : Term := ((openm! "eq" #𝓋[ gt#"Bool" ] (Vec.to (#𝓋[ iBool ]))) • TrueCtor) • TrueCtor
#eval t2.eval_loop EqBoolCtx

def t3 : Term := ((openm! "eq" #𝓋[ gt#"Bool" ] (Vec.to (#𝓋[ iBool ]))) • TrueCtor) • FalseCtor
#eval t3.eval_loop EqBoolCtx


end Core.Examples
