import Surface.Ty
import Surface.Global
import Surface.Term

import Surface.Examples.Boolean

import Translation.Global

namespace Surface.Examples.Maybe


def NothingPat : Core.Pattern 1 := #(⟨"Nothing", 1, #(t#0), 0, 0⟩)
def JustPat : Core.Pattern 1 := #(⟨"Just", 1, #(t#0), 0, 1⟩)

def NothingNothingPat : Core.Pattern 2 :=  NothingPat ++ NothingPat
def JustJustPat : Core.Pattern 2 :=  JustPat ++ JustPat
def JustNothingPat : Core.Pattern 2 :=  JustPat ++ NothingPat
def NothingJustPat : Core.Pattern 2 :=  NothingPat ++ JustPat


def mbenv : GlobalEnv := [

  -- eqMB_poly : ∀ a. Eq a -> Maybe a -> Maybe  a -> Bool = eq
  .defn "eqMB_poly" (∀[★] (gt#"Eq" • t#0) -:> (gt#"Maybe" • t#0) -:> ((gt#"Maybe" • t#0) -:> (gt#"Bool")))
    (Λˢ[★] λˢ[gt#"Eq" • t#0] g`#"eq" `•ᵤ #(gt#"Maybe" • t#0) `•ₑ #() `•ₜ .nil) ,

  -- MBI : ∀ t u, t ~ Maybe u -> Eq u -> Eq t
  -- instance Eq (Maybe a) | Eq a where eq = ...
  .instDecl "MBI" ⟨1, #(★), 1, #(★), 2, #(t#1 ~[★]~ (gt#"Maybe" • t#0), gt#"Eq" • t#0), gt#"Eq" • t#1⟩
                  [("eq", (λˢ[gt#"Maybe" • t#0] λˢ[gt#"Maybe" • t#0]
                          mtch' #((`#1, gt#"Maybe" • t#0), (`#0, gt#"Maybe" • t#0))
                          #( (JustJustPat,       (((g`#"eq" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil) `• `#0 :: t#0) `• `#1 :: t#0))
                           , (NothingNothingPat, Surface.Examples.Boolean.TrueCtor)
                           , (JustNothingPat,    Surface.Examples.Boolean.FalseCtor)
                           , (NothingJustPat,    Surface.Examples.Boolean.FalseCtor)
                           )))],
  -- data Maybe a = Just a | Nothing
  .data (n := 2) "Maybe" (★ -:> ★) #(("Just", ⟨1, #(★), 0, #(), 1, #(t#0), gt#"Maybe" • t#0⟩ ),
                                     ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩))
  ] ++ Surface.Examples.Boolean.benv

#eval mbenv

def Γ := do
  let benv' <- (Translation.translate_SI mbenv)
  Translation.translate_IC benv'

#eval! Γ

#guard (do let Γ <- Γ
           return Γ.wf_globals) == .ok ()


end Surface.Examples.Maybe
