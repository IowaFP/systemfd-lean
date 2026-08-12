import Surface.Ty
import Surface.Global
import Surface.Term

import Translation.Global

namespace Surface.Examples.Boolean

def benv : GlobalEnv := [

  -- .instDecl  "IdI" ⟨1, #(`★), 0, #(), 2, #(t`#0, t`#0), (gt`#"Id" `• t`#0) `• t`#0 ⟩ #(),
  -- .classDecl "Id" #(`★, `★) #() #(("fd", (0, 1)), ("bwk", (1, 0))) #(),

  -- .instDecl "EqBoolI" ⟨1, #(`★), 0, #(), 1, #(gt`#"Bool"), gt`#"Eq" `• t`#0⟩ #(("eq", λˢ[gt`#"Bool"] λˢ[gt`#"Bool"] `#0)),
  -- .classDecl "Eq" #(`★) #() #() #(("eq",  ⟨0, #(), 0, #(), 0, #(), t`#0 `-:> (t`#0 `-:> gt`#"Bool")⟩)),
  .data (n := 2) "Bool" `★ #(("True", ⟨0, #(), 0, #(), 0,  #(), gt`#"Bool"⟩), ("False", ⟨0, #(), 0, #(), 0, #(), gt`#"Bool"⟩))
  ]

#eval benv

#eval Translation.translate_SI benv

end Surface.Examples.Boolean
