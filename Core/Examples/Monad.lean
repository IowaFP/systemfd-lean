import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Algorithm.Kind

import Core.Typing

namespace Monad.List
/- data Bool = True | False -/
def BoolCtx : List Global := [
  .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]
  ]
#guard infer_kind BoolCtx [] (gt#"Bool") == .some ★
#guard infer_kind BoolCtx [] (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") == .some ★
#guard infer_kind BoolCtx [] (gt#"Bool" =:> gt#"Bool" -:> gt#"Bool") == none
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
         v[ g# "False", g# "True" ]

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
  match!  #1
   v[ "True", "False" ]
   v[ match! #0 v[ "True", "False" ] v[ g#"True", g#"False" ] ,
      match! #0 v[ "True", "False" ] v[ g# "False", g# "False"]
    ]

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
  .openm "bind" (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) =:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))),

  -- return : ∀ m a. Monad m => a -> m a
  .openm "return" (∀[★ -:> ★] ∀[★] (gt#"Monad" • t#1) =:> t#0 -:> (t#1 • t#0)),

  -- class Monad (m : ★ → ★)
  .opent "Monad" ((★ -:> ★) -:> ◯)
]


theorem test :
  Kinding ListCtx []
        (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) =:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0))) ★ :=
by
  constructor; constructor; constructor
  constructor
  · constructor;
    · constructor; unfold ListCtx; simp; unfold lookup_kind; unfold Option.map; unfold lookup; simp; unfold Vec.fold;
      simp; unfold Vec.uncons; simp; unfold Vec.fold; simp; unfold Vec.drop; simp; unfold Vec.uncons; simp;
      unfold lookup; simp; unfold lookup; simp; unfold lookup; simp; unfold Entry.kind; simp; rfl
    · unfold ListCtx; constructor; simp;
  · constructor
    · constructor; simp
    · constructor
      · constructor
        · constructor; simp
        · constructor
          · constructor; simp; rfl
          · constructor; simp
      · constructor
        · constructor; simp; rfl
        · constructor; simp

#guard infer_kind ListCtx [] (∀[★ -:> ★] ∀[★] ∀[★] (gt#"Monad" • t#2) =:> (t#1 -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0)))
       == some ★

end Monad.List
