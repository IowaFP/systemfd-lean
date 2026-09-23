import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global

namespace Surface.Examples.Boolean

def benv : GlobalEnv := [
  -- .defn "test" (gt#"Bool" -:> gt#"Bool") ((g`#"eq" `•ᵤ #(gt#"Bool") `•ₑ #() `•ₜ .nil) `• (g`#"True" `•ᵤ #() `•ₑ #() `•ₜ .nil) :: gt#"Bool"),

  -- .defn "eqB" (gt#"Bool" -:> (gt#"Bool" -:> gt#"Bool")) (g`#"eq" `•ᵤ #(gt#"Bool") `•ₑ #() `•ₜ .nil) ,

  .instDecl "OrdBoolI" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), gt#"Ord" • t#0⟩ [("leq", (λˢ[gt#"Bool"] λˢ[gt#"Bool"] (g`#"LT" `•ᵤ #() `•ₑ #() `•ₜ .nil)))],

  .instDecl "EqBoolI" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), gt#"Eq" • t#0⟩ [("eq", λˢ[gt#"Bool"] λˢ[gt#"Bool"] `#0)],

  .classDecl "Ord" #(★) /-[("supOrd", "Eq", [0])] []-/ [("leq", ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Ordering")⟩)],

  .classDecl "Eq" #(★) /-[] []-/ [("eq",  ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Bool")⟩)],

  .data (n := 2) "Bool" ★ #(("True", ⟨0, #(), 0, #(), 0,  #(), gt#"Bool"⟩),
                            ("False", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩)),
  .data (n := 3) "Ordering" ★ #( ("LT", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩)
                               , ("EQ", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩)
                               , ("GT", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩)),

  .data (n := 2) "Maybe" (★ -:> ★) #(("Just", ⟨1, #(★), 0, #(), 1, #(t#0), gt#"Maybe" • t#0⟩ ),
                                     ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩))
  ]

#eval benv
#eval  Translation.translate_SI benv
#eval! do
  let benv' <- (Translation.translate_SI benv)
  Translation.translate_IC benv'

#guard (do
  let benv' <- (Translation.translate_SI benv)
  let benv'' <- Translation.translate_IC benv'
  Translation.Option.toTM "wf" $ benv''.wf_globals) == .ok ()


def Γ := do
  let benv' <- (Translation.translate_SI benv)
  Translation.translate_IC benv'


#eval! do
  let Γ <- Γ
  -- Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [] (gt#"Eq" • gt#"Bool")
  Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [★] (gt#"Eq" • (gt#"Maybe" • t#0))
  -- Translation.Option.toTM "synth_term" $ Translation.Core.Ty.synth_term Γ [] [] (gt#"Eq" • gt#"Bool")

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


end Surface.Examples.Boolean
