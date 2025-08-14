import Hs.Translator.HsTerm


namespace Translator.HsTerm.Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

    #guard wf_ctx Γ == .some ()

    #guard (compile_term Γ (∀[★](#6 `@k #0) -t> #1 -t> #2 -t> #10) `#0) == .ok #0
    #guard (compile_term Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6)) == .ok (#0 `@t #6)

    #eval! DsM.run (compile_term Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6))


    #guard (compile_term Γ (#5 `@k #6) (.HsHole (`#5 `•k `#6))) == .ok (#4 `@t #6 `@ (refl! ★ #6))

    #guard (compile_term Γ (#6 -t> #7 -t> #8) (`#0 `•t `#6 `• (.HsHole (`#5 `•k `#6)))) ==
                  .ok (#0 `@t #6 `@ (#4 `@t #6 `@ (refl! ★ #6)))

end Translator.HsTerm.Test
