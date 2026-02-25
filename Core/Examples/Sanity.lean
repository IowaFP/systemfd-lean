import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer


namespace Core.Examples
/- data Bool = True | False -/
def BoolCtx : Core.GlobalEnv := [
  .data (n := 2) "Bool" ★ [ ("True", gt#"Bool") , ("False", gt#"Bool") ]
  ]

#guard Ty.infer_kind BoolCtx [] (gt#"Bool") == .some ★
#guard Ty.infer_kind BoolCtx [] (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") == .some ★

#eval! (g#"True").infer_type BoolCtx [] []

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/

def notTerm : Core.Term := λ[gt#"Bool" ]
  match! 1 #0
         [ g#"True" ]
         [ g# "False"]
         g#"True"

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
  match! 2 #1
    [ g#"True", g#"False" ]
    [
      match! 2 #0 [ g#"True", g#"False" ] [ g#"True", g#"False" ] `0,
      match! 2  #0 [ g#"True", g#"False" ] [ g# "False", g# "False"] `0
    ]
    `0

def funs : GlobalEnv := [ .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool ]
def EqBoolCtx : GlobalEnv := funs ++ BoolCtx

#eval! eqBool.infer_type EqBoolCtx [] []
#guard Globals.wf_globals EqBoolCtx == some ()

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
