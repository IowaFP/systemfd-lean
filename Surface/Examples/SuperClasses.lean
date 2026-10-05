import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global
import Surface.Examples.Boolean

namespace Surface.Examples.Boolean

def benv_ord : GlobalEnv := [


  .defn "test_ord_eq_bool" ((gt#"Ord" • gt#"Bool") -:> gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") (λˢ[gt#"Ord" • gt#"Bool"] g`#"eq" `•ᵤ #(gt#"Bool") `•ₑ #() `•ₜ .nil),

  -- cannot use this function unfortunately
  .defn "test_ord_eq" (∀[★] (gt#"Ord" • t#0) -:> t#0 -:> t#0 -:> gt#"Bool") (Λˢ[★] λˢ[gt#"Ord" • t#0] g`#"eq" `•ᵤ #(t#0) `•ₑ #() `•ₜ .nil),

  .instDecl "OrdBoolI" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), gt#"Ord" • t#0⟩
    [("leq", (λˢ[gt#"Bool"] λˢ[gt#"Bool"]
         mtch' #((`#1, gt#"Bool"), (`#0,  gt#"Bool"))
              #( (TrueTruePat, EQCtor)
               , (FalseFalsePat, EQCtor)
               , (TrueFalsePat, GTCtor)
               , (FalseTruePat, LTCtor)
               )))],

  .classDecl "Ord" #(★) /- [] -/ [("supOrdEq", "Eq", [0])] [("leq", ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Ordering")⟩)],

  ] ++ benv

#eval benv_ord
#eval  Translation.translate_SI benv_ord
#eval! do
  let benv' <- (Translation.translate_SI benv_ord)
  Translation.translate_IC benv'


-- #eval! do
--   let benv' <- Translation.translate_SI benv_ord
--   let benv'' <- Translation.translate_IC benv'
--   Translation.Option.toTM "wf" $ Core.GlobalEnv.wf_globals benv''

#guard (do
  let benv' <- Translation.translate_SI benv_ord
  let benv'' <- Translation.translate_IC benv'
  Translation.Option.toTM "wf" $ benv''.wf_globals) == .ok ()


-- def Γ := do
--   let benv' <- (Translation.translate_SI benv)
--   Translation.translate_IC benv'

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
