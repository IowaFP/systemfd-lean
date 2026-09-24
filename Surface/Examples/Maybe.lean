import Surface.Ty
import Surface.Global
import Surface.Term

import Surface.Examples.Boolean

import Translation.Global

namespace Surface.Examples.Maybe

def mbenv : GlobalEnv := [

  -- .instDecl "OrdBoolI" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), gt#"Ord" • t#0⟩ [("leq", (λˢ[gt#"Bool"] λˢ[gt#"Bool"] (g`#"LT" `•ᵤ #() `•ₑ #() `•ₜ .nil)))],

  -- MBI : ∀ t u, t ~ Maybe u -> Eq u -> Eq t
  .instDecl "MBI" ⟨1, #(★), 1, #(★), 2, #(t#1 ~[★]~ (gt#"Maybe" • t#0), gt#"Eq" • t#0), gt#"Eq" • t#0⟩ [("eq", λˢ[gt#"Maybe" • t#0] λˢ[gt#"Maybe" • t#0] (g`#"eq" `•ᵤ #(gt#"Maybe" • t#0) `•ₑ #(t#0) `•ₜ .nil))],

  .data (n := 2) "Maybe" (★ -:> ★) #(("Just", ⟨1, #(★), 0, #(), 1, #(t#0), gt#"Maybe" • t#0⟩ ),
                                     ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩))
  ] ++ Surface.Examples.Boolean.benv

#eval mbenv
-- #eval!  Translation.translate_SI mbenv
-- #eval! do
--   let benv' <- (Translation.translate_SI mbenv)
--   Translation.translate_IC benv'

def Γ := do
  let benv' <- (Translation.translate_SI mbenv)
  Translation.translate_IC benv'


#eval! do
  let Γ <- Γ
  -- Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [] (gt#"Eq" • gt#"Bool")
  Translation.Option.toTM "ford" $ Core.Synth.Ty.ford Γ [★] (gt#"Eq" • (gt#"Maybe" • t#0))
  -- Translation.Option.toTM "synth_term" $ Translation.Core.Ty.synth_term Γ [] [] (gt#"Eq" • gt#"Bool")

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


end Surface.Examples.Maybe
