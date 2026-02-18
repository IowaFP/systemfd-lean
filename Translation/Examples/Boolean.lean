
import Surface.Term
import Surface.Global
import Translation.Global


def Surface.BoolCtx : List Surface.Global := [
  .data "Bool" `★ v[ ("True", gt`#"Bool") , (("False"), gt`#"Bool") ]
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
         v[ g`#"True", g`#"False" ]
         v[ g`# "False", g`# "True" ]
         g`#"False"

/-  eqBool =
  λ x. λ y. case x of
              True → case y of
                       True → True
                       False → False
              False → case y of
                       True → False
                       False → True
 -/
def Surface.eqBool : Term := λˢ[ .global "Bool" ] λˢ[ .global "Bool" ]
  matchˢ! `#1
   v[ g`#"True", g`#"False" ]
   v[ matchˢ! `#0 v[ g`#"True", g`#"False" ] v[ g`#"True", g`#"False"] g`#"False",
      matchˢ! `#0 v[ g`#"True", g`#"False" ] v[ g`# "False", g`# "False"] g`#"False"
    ]
    g`#"False"

#eval trans_globals Surface.BoolCtx
#eval do let gs' <- trans_globals Surface.BoolCtx
         let t' <- trans_term gs' [] [] Surface.eqBool
         return t'
