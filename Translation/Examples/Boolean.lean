
import Surface.Term
import Surface.Global
import Translation.Global
import Translation.Term
import Core.Vec


def Surface.BoolCtx : Surface.GlobalEnv := [
  .data "One" `★ ([ ("1" , gt`#"One")] : Vect 1 (String × Ty)),
  .data "Bool" `★ ([ ("True", gt`#"Bool") , (("False"), gt`#"Bool") ] : Vect 2 (String × Ty))
 ]

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/
def Surface.notTerm : Surface.Term := λˢ[ .global "Bool" ]
  matchˢ! `#0
         ([ g`#"True", g`#"False" ] : Vect 2 Term)
         ([ g`# "False", g`# "True" ])
         g`#"False"

/-  eqBool =
  λ x. λ y. case x ofasdf
              True → case y of
                       True → True
                       False → False
              False → case y of
                       True → False
                       False → True
 -/
def Surface.eqBool : Term := λˢ[ .global "Bool" ] λˢ[ .global "Bool" ]
  matchˢ! `#1
   ([ g`#"True", g`#"False" ] : Vect 2 Term)
   ([ matchˢ! `#0 ([ g`#"True", g`#"False" ] : Vect 2 Term) [ g`#"True", g`#"False"] g`#"False",
      matchˢ! `#0 ([ g`#"True", g`#"False" ] : Vect 2 Term) [ g`# "False", g`# "False"] g`#"False"
    ])
    g`#"False"


-- #eval Surface.BoolCtx.infer
#eval Surface.GlobalEnv.translate Surface.BoolCtx

#eval do let gs' <- Surface.BoolCtx.translate
         let t' <- Surface.eqBool.translate gs' [] []
         return t'
