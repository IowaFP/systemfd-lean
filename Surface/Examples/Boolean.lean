import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global

namespace Surface.Examples.Boolean

def benv : GlobalEnv := [

  -- .instDecl  "IdI" ⟨1, #(`★), 0, #(), 2, #(t`#0, t`#0), (gt`#"Id" `• t`#0) `• t`#0 ⟩ #(),
  -- .classDecl "Id" #(★, ★) [] [⟨"fd", 0, #(0), 1⟩, ⟨"bwk", 0, #(1), 0⟩] [],
  .instDecl "OrdBoolI" ⟨1, #(★), 0, #(), 1, #(gt#"Bool"), gt#"Ord" • t#0⟩ [("leq", (λˢ[gt#"Bool"] λˢ[gt#"Bool"] (g`#"LT")))],
  .instDecl "EqBoolI" ⟨1, #(★), 0, #(), 1, #(gt#"Bool"), gt#"Eq" • t#0⟩ [("eq", λˢ[gt#"Bool"] λˢ[gt#"Bool"] `#0)],

  .classDecl "Ord" #(★) /-[("supOrd", "Eq", [0])] []-/ [("leq", ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Ordering")⟩)],
  .classDecl "Eq" #(★) /-[] []-/ [("eq",  ⟨0, #(), 0, #(), 0, #(), t#0 -:> (t#0 -:> gt#"Bool")⟩)],
  .data (n := 2) "Bool" ★ #(("True", ⟨0, #(), 0, #(), 0,  #(), gt#"Bool"⟩),
                            ("False", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩)),
  .data (n := 3) "Ordering" ★ #( ("LT", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩)
                               , ("EQ", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩)
                               , ("GT", ⟨0, #(), 0, #(), 0,  #(), gt#"Ordering"⟩))
  ]

#eval benv
#eval  Translation.translate_SI benv
#eval! do
  let benv' <- (Translation.translate_SI benv)
  Translation.translate_IC benv'


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
