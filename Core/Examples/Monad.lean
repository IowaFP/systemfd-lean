import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Kind

import Core.Typing

namespace Monad.List
/- data Bool = True | False -/
def BoolCtx : List Global := [
  .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]
  ]
#guard Ty.infer_kind BoolCtx [] (gt#"Bool") == .some ★
#guard Ty.infer_kind BoolCtx [] (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") == .some ★

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/
def notTerm : Term := λ[ .global "Bool" ]
  match! #0
         v[ g#"True", g#"False" ]
         v[ g# "False", g# "True" ]
         g#"False"

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
  match!  #1
   v[ g#"True", g#"False" ]
   v[ match! #0 v[ g#"True", g#"False" ] v[ g#"True", g#"False" ] g#"False",
      match! #0 v[ g#"True", g#"False" ] v[ g# "False", g# "False"] g#"False"
    ]
   g#"False"

def EqBoolCtx := [.defn "notTerm" (gt#"Bool" -:> gt#"Bool") notTerm,
                  .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool] ++ BoolCtx


def ListCtx : List Global := [
  -- data List a
  -- | Nil : ∀a. List a
  -- | Cons : ∀a. a → List a → List a
  .data "List" (★ -:>  ★)
  v[ ("Nil", ∀[★] (gt#"List" • t#0))
   , ("Cons", ∀[★] (t#0 -:> (gt#"List" • t#0) -:> (gt#"List" • t#0))) ],

  -- bind : ∀ m a b. Monad m => a → (a -> m b) -> m b
  .openm "bind" (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) -:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))),

  -- return : ∀ m a. Monad m => a -> m a
  .openm "return" (∀[★ -:> ★] ∀[★] (gt#"Monad" • t#1) -:> t#0 -:> (t#1 • t#0)),

  -- class Monad (m : ★ → ★)
  .opent "Monad" ((★ -:> ★) -:> ◯)
]


#guard (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) -:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))).infer_kind ListCtx []
       == some ★

end Monad.List
