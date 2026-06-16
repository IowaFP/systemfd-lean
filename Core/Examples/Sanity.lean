import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer


namespace Core.Examples
/- data Bool = True | False -/
def BoolCtx : GlobalEnv := [
  Global.data 2 "Bool" ★
             #𝓋[ ("True", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)
               , ("False", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)]
  ]

def TrueCtor : Term := ctor! "True" #𝓋[] .nil
def FalseCtor : Term := ctor! "False" #𝓋[] .nil

#guard Ty.infer_kind BoolCtx [] (gt#"Bool") == .some ★
#guard Ty.infer_kind BoolCtx [] (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") == .some ★

#eval! BoolCtx.wf_globals

#eval! TrueCtor.infer_type BoolCtx [] []

#eval spine_kinding [Global.data 0 "Bool" ★ #𝓋[]] (.data .cls) "True" ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩
#eval lookup_ctor? [Global.data 0 "Bool" ★ #𝓋[]] .cls "True" gt#"Bool"

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

-- #eval! eqBool.infer_type EqBoolCtx [] []
-- #guard Globals.wf_globals EqBoolCtx == some ()

-- def t1 := Term.match g#"False"
--               v[ "True", "False" ] v[ g#"False" , g#"True" ]

-- def t2 := Term.match g#"True"
--               v[ "True", "False" ]  v[ g#"True" , g#"False" ]


-- #eval ctor_idx "True" EqBoolCtx
-- #eval Fin.ofNat 2 0


-- #eval ctor_idx "False" EqBoolCtx
-- #eval Fin.ofNat 2 1


-- #eval [ g#"True", g#"False"] 0 -- g#"True"

-- #eval [ g#"True", g#"False"] 1 -- g#"False"

-- #guard eval EqBoolCtx t1 == g#"True"
-- #guard eval EqBoolCtx t2 == g#"True"

end Core.Examples
