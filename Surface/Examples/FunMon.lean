import Surface.Ty
import Surface.Global
import Surface.Term

import Surface.Examples.Boolean

import Translation.Global

namespace Surface.Examples.FunMon


def NothingPat : Core.Pattern 1 := #(⟨"Nothing", 1, #(t#1), 0, 0⟩)
def JustPat : Core.Pattern 1 := #(⟨"Just", 1, #(t#1), 0, 1⟩)

def NothingNothingPat : Core.Pattern 2 :=  NothingPat ++ NothingPat
def JustJustPat : Core.Pattern 2 :=  JustPat ++ JustPat
def JustNothingPat : Core.Pattern 2 :=  JustPat ++ NothingPat
def NothingJustPat : Core.Pattern 2 :=  NothingPat ++ JustPat


def mbenv : GlobalEnv := [

  -- instance Monad Maybe where { return = ... ; bind = ... }
  .instDecl "MM" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"Maybe"), (gt#"Monad" • t#0)⟩
    [ ("return", Λˢ[★]λˢ[t#0] (g`#"Just" `•ᵤ #(t#0) `•ₑ #() `•ₜ #(`#0).to))
    , ("bind", Λˢ[★]Λˢ[★]λˢ[(gt#"Maybe" • t#1)]λˢ[(t#1 -:> (gt#"Maybe" • t#0))]
                  mtch' #((`#1, gt#"Maybe" • t#1))
                    #( (JustPat,    Surface.Term.app `#1 `#0 t#1),
                       (NothingPat,  g`#"Nothing" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil))
      )
    ],

  -- class Monad m | Functor m where { return : ∀ a. a -> m a ;  bind : ∀ a b. m a -> (a -> m b) -> m b }
  .classDecl "Monad" #(★ -:> ★) [ ("supMonFun", "Functor", [0]) ]
    [ ("return", ⟨0, #(), 0, #(), 0, #(), ∀[★] t#0 -:> (t#1 • t#0)⟩)
    , ("bind", ⟨0, #(), 0, #(), 0, #(), (∀[★]∀[★] (t#2 • t#1) -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0)) ⟩)
    ],


  -- FM : ∀ t, t ~ Maybe -> Functor t
  -- instance Functor Maybe where fmap = ...
  .instDecl "FM" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"Maybe"), (gt#"Functor" • t#0)⟩
    [("fmap", Λˢ[★]Λˢ[★]λˢ[t#1 -:> t#0] λˢ[gt#"Maybe" • t#1]
                  mtch' #((`#0, gt#"Maybe" • t#1))
                    #( (JustPat,    (g`#"Just" `•ᵤ #(t#0) `•ₑ #() `•ₜ #(Surface.Term.app `#2 `#0 t#1).to)),
                       (NothingPat,  g`#"Nothing" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil)))],

  -- class Functor f where fmap :: ∀ a b. (a -> b) -> f a -> f b
  .classDecl "Functor" #(★ -:> ★) [] [("fmap", ⟨0, #(), 0, #(), 0, #(), (∀[★]∀[★]((t#1 -:> t#0) -:> ((t#2 • t#1) -:> (t#2 • t#0)))) ⟩)],

  -- data Maybe a = Just a | Nothing
  .data (n := 2) "Maybe" (★ -:> ★) #(("Just", ⟨1, #(★), 0, #(), 1, #(t#0), gt#"Maybe" • t#0⟩ ),
                                     ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩))
  ]

#eval mbenv
#eval!  Translation.translate_SI mbenv
def Γ := do
  let benv' <- (Translation.translate_SI mbenv)
  Translation.translate_IC benv'

#eval! Γ

#guard (do let Γ <- Γ
           return Γ.wf_globals) == .ok ()


end Surface.Examples.FunMon
