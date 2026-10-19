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
  .instDecl "MM" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"Maybe"), (gt#"Monad" • t#0)⟩
    [ ("return", Λˢ[★]λˢ[t#0] (g`#"Just" `•ᵤ #(t#0) `•ₑ #() `•ₜ #(`#0).to))
    -- , ("bind", sorry)
    ],

  .classDecl "Monad" #(★ -:> ★) [ ("supMonFun", "Functor", [0]) ]
    [ ("return", ⟨0, #(), 0, #(), 0, #(), ∀[★] t#0 -:> (t#1 • t#0)⟩)
    -- , ("bind", ⟨0, #(), 0, #(), 0, #(), (∀[★]∀[★] (t#2 • t#1) -:> (t#1 -:> (t#2 • t#0)) -:> (t#2 • t#0)) ⟩)
    ],


  -- FM : ∀ t, t ~ Maybe -> Functor t
  .instDecl "FM" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"Maybe"), (gt#"Functor" • t#0)⟩
    [("fmap", Λˢ[★]Λˢ[★]λˢ[t#1 -:> t#0] λˢ[gt#"Maybe" • t#1]
                  mtch' #((`#0, gt#"Maybe" • t#1))
                    #( (JustPat,    (g`#"Just" `•ᵤ #(t#0) `•ₑ #() `•ₜ #(Surface.Term.app `#2 `#0 t#1).to)),
                       (NothingPat,  g`#"Nothing" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil)))],

  .classDecl "Functor" #(★ -:> ★) [] [("fmap", ⟨0, #(), 0, #(), 0, #(), (∀[★]∀[★]((t#1 -:> t#0) -:> ((t#2 • t#1) -:> (t#2 • t#0)))) ⟩)],


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

-- #eval! do
--   let Γ <- Γ
--   -- Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [] (gt#"Eq" • gt#"Bool")
--   Translation.Option.toTM "ford" $ (Core.Synth.Ty.ford Γ [★] (gt#"Eq" • (gt#"Maybe" • t#0))).map (Core.SpineTy.repr ·)
--   -- Translation.Option.toTM "synth_term" $ Translation.Core.Ty.synth_term Γ [] [] (gt#"Eq" • gt#"Bool")

-- #guard (do
--   let benv' <- (Translation.translate_SI benv)
--   let benv'' <- Translation.translate_IC benv'
--   Translation.Option.toTM "wf" $ benv''.wf_globals) == .ok ()


-- #eval! do
--   let Γ <- Γ
--   -- Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [] (gt#"Eq" • gt#"Bool")
--   Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [★] (gt#"Eq" • (gt#"Maybe" • t#0))
--   -- Translation.Option.toTM "synth_term" $ Translation.Core.Ty.synth_term Γ [] [] (gt#"Eq" • gt#"Bool")

-- #eval!
--   do
--   let benv' <- (Translation.translate_SI benv)
--   let benv'' <- Translation.translate_IC benv'

--   -- Translation.Option.toTM "lookup"  (match ((Core.lookup "LT" benv'')) with
--   -- | .some (.ctor x' _ ⟨0, _, 0, _, 0, _, R⟩) => do
--   --   let c <- Core.Ty.synth_coercion benv'' [] [] R gt#"Ordering"
--   --   return (Core.Term.cast t#0 c (ctor! "LT" #() #() .nil))
--   -- | _ => none)
--   Translation.Option.toTM "test" (Core.Synth.synth_coercion_term benv'' [★] [t#0 ~[★]~ gt#"Bool"] ((t#0 -:> gt#"Ordering") ~[★]~ (gt#"Bool" -:> gt#"Ordering")))
--   -- Translation.Option.toTM "test" ((λˢ[gt#"Bool"] (g`#"LT")).type_directed_translate benv'' [★] [gt#"Bool", t#0 ~[★]~ gt#"Bool"] (t#0 -:> gt#"Ordering"))


end Surface.Examples.FunMon
