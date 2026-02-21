import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Kind

import Core.Typing

namespace Core.Examples.Monad
/- data Bool = True | False -/
def BoolCtx : List Global := [
  .data "Bool" ★ ([ ("True", gt#"Bool") , (("False"), gt#"Bool")]  : Vect 2 (String × Ty))
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
         [ g#"True", g#"False" ]
         ([ g# "False", g# "True" ] : Vect 2 Term)
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
   [ g#"True", g#"False" ]
   ([ match! #0 [ g#"True", g#"False" ] ([ g#"True", g#"False" ] : Vect 2 Term) g#"False",
      match! #0 [ g#"True", g#"False" ] ([ g# "False", g# "False"] : Vect 2 Term) g#"False"
   ] : Vect 2 Term)
   g#"False"

def EqBoolCtx := [.defn "notTerm" (gt#"Bool" -:> gt#"Bool") notTerm,
                  .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") eqBool] ++ BoolCtx


def ListCtx : List Global := [
  -- data List a
  -- | Nil : ∀a. List a
  -- | Cons : ∀a. a → List a → List a
  .data "List" (★ -:>  ★)
  ([ ("Nil", ∀[★] (gt#"List" • t#0))
   , ("Cons", ∀[★] (t#0 -:> (gt#"List" • t#0) -:> (gt#"List" • t#0))) ] : Vect 2 (String × Ty)),

  -- bind : ∀ m a b. Monad m => a → (a -> m b) -> m b
  .openm "bind" (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) -:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))),

  -- return : ∀ m a. Monad m => a -> m a
  .openm "return" (∀[★ -:> ★] ∀[★] (gt#"Monad" • t#1) -:> t#0 -:> (t#1 • t#0)),

  -- class Monad (m : ★ → ★)
  .opent "Monad" ((★ -:> ★) -:> ◯)
]


#guard (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) -:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))).infer_kind ListCtx []
       == some ★

end Core.Examples.Monad
