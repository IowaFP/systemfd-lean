import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep

def FunDepsCtx : List Global := [

  -- id :: ∀ A B. Equal A B -> A -> B =
  --     Λ A B. λ i a. a |> fdEqual1 A A B (EqualTT A A (refl A)) i
  .defn "id" (∀[★]∀[★] ((gt#"Equal" • t#1) • t#0) -:> t#1 -:> t#0) (
    Λ[★]Λ[★] λ[ BaseKind.open , ((gt#"Equal" • t#1) • t#0) ] λ[BaseKind.closed, t#1]
      (#0 ▹ ((((g#"fdFwd" •[t#1]) •[t#1]) • (((g#"EqualTT" •[t#1]) •[t#1]) • (refl! t#1))) • #1))
  ),
  -- instance fdEqual2 = Λ t t' u. λ i1 i2.
  --     guard EqualTT[t, u] <- i1 then λ c1.
  --     guard EqualTT[t', u] <- i2 then λ c2.
  --         c1 ; sym c2
  .inst "fdBwk" (Λ[★]Λ[★]Λ[★] λ[BaseKind.open, (gt#"Equal" • t#2) • t#0] λ[BaseKind.open, (gt#"Equal" • t#1) • t#0 ]
    .guard ((g#"EqualTT" •[t#2]) •[t#0]) #1 (λ[.closed, t#2 ~[★]~ t#0]
      .guard ((g#"EqualTT" •[t#1]) •[t#0]) #1 (λ[.closed, t#1 ~[★]~ t#0]
            #1 `; sym! #0)
    )
  ),

  -- instance fdEqual1 = Λ t u u'. λ i1 i2.
  --     guard EqualTT[t, u] <- i1 then λ c1.
  --     guard EqualTT[t, u'] <- i2 then λ c2.
  --         sym c1 ; c2
  .inst "fdFwd" (Λ[★]Λ[★]Λ[★] λ[BaseKind.open, (gt#"Equal" • t#2) • t#1] λ[BaseKind.open, (gt#"Equal" • t#2) • t#0 ]
    .guard ((g#"EqualTT" •[t#2]) •[t#1]) #1 (λ[.closed, t#2 ~[★]~ t#1]
      .guard ((g#"EqualTT" •[t#2]) •[t#0]) #1 (λ[.closed, t#2 ~[★]~ t#0]
            sym! #1 `; #0)
    )
  ),


  -- instance EqualTT :: ∀ t u. t ~ u -> Equal t u
  .instty "EqualTT" (∀[★]∀[★] t#1 ~[★]~ t#0 -:> ((gt#"Equal" • t#1) • t#0)),

  -- open fdBwk :: ∀ t t' u. Equal t u -> Equal t' u -> t ~ t'
  .openm "fdFwd" (∀[★] ∀[★] ∀[★] ((gt#"Equal" • t#2) • t#0) =:>  ((gt#"Equal" • t#1) • t#0) -:> (t#2 ~[★]~ t#1)),
  -- open fdFwd :: ∀ t u u'. Equal t u -> Equal t u' -> u ~ u'
  .openm "fdFwd" (∀[★] ∀[★] ∀[★] ((gt#"Equal" • t#2) • t#1) =:>  ((gt#"Equal" • t#2) • t#0) -:> (t#1 ~[★]~ t#0)),

  .opent "Equal" (★ -:> ★ -:> ◯)

]
