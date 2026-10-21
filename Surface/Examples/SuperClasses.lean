import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global
import Surface.Examples.Boolean
import Surface.Examples.Maybe

namespace Surface.Examples.Boolean

def benv_ord : GlobalEnv := [

  -- test_ord_eq_poly : ∀ a. Ord a -> Maybe a -> Maybe a -> Bool = eq @(Maybe a)
  .defn "test_ord_eq_poly" (∀[★](gt#"Ord" • t#0) -:> (gt#"Maybe" • t#0) -:> (gt#"Maybe" • t#0) -:> (gt#"Bool"))
    (Λˢ[★] λˢ[gt#"Ord" • t#0] g`#"eq" `•ᵤ #(gt#"Maybe" • t#0) `•ₑ #() `•ₜ .nil),


  -- test_ord_eq_bool : Bool -> Bool -> Bool = eq @Bool
  .defn "test_ord_eq_bool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool")
    (g`#"eq" `•ᵤ #(gt#"Bool") `•ₑ #() `•ₜ .nil),

  -- test_ord_eq : ∀ a. Ord a -> a -> a -> Bool = eq @a
  .defn "test_ord_eq" (∀[★] (gt#"Ord" • t#0) -:> t#0 -:> t#0 -:> gt#"Bool") (Λˢ[★] λˢ[gt#"Ord" • t#0] g`#"eq" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil),

  -- instance Ord Bool where leq = ...
  .instDecl "OrdBoolI" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), gt#"Ord" • t#0⟩
    [("leq", (λˢ[gt#"Bool"] λˢ[gt#"Bool"]
         mtch' #((`#1, gt#"Bool"), (`#0,  gt#"Bool"))
              #( (TrueTruePat, EQCtor)
               , (FalseFalsePat, EQCtor)
               , (TrueFalsePat, GTCtor)
               , (FalseTruePat, LTCtor)
               )))],

  -- class Ord a | Eq a where leq :: a -> a -> Ordering
  .classDecl "Ord" #(★) /- [] -/ [("supOrdEq", "Eq", [0])] [("leq", ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Ordering")⟩)],

  ] ++ Surface.Examples.Maybe.mbenv

#eval benv_ord
#eval  Translation.translate_SI benv_ord
#eval! do
  let benv' <- (Translation.translate_SI benv_ord)
  Translation.translate_IC benv'


#guard (do
  let benv' <- Translation.translate_SI benv_ord
  let benv'' <- Translation.translate_IC benv'
  Translation.Option.toTM "wf" $ benv''.wf_globals) == .ok ()

#guard (do
  let benv' <- Translation.translate_SI benv_ord
  let benv'' <- Translation.translate_IC benv'
  Translation.Option.toTM "wf" $ benv''.check_open_exhaustive) == .ok ()


end Surface.Examples.Boolean
