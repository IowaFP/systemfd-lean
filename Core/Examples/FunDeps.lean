import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Infer.Global
import Core.Examples.Common

namespace Core.Examples

def FunDepsCtx : GlobalEnv := [

  -- id :: ∀ A B. Equal A B -> A -> B =
  --     Λ A B. λ i a. a |> fdEqual1 A A B (EqualTT A A (refl A)) i
  .defn "id" (∀[★]∀[★] ((gt#"Equal" • t#1) • t#0) -:> t#1 -:> t#0) (
    Λ[★]Λ[★]λ[(gt#"Equal" • t#1) • t#0]λ[t#1]
      let i := inst! "EqualTT" #(t#1, t#1) #() #(refl! t#1).to
      let t0 := openm! "fdFwd" #(t#1, t#1, t#0) #() #(i, #1).to
      Term.cast t#0 t0 #0
      -- (.cast (t#0) (open! "fdFwd" #(t#1, t#1, t#0) #() #((inst! "EqualTT" #(t#1, t#1)  #(refl! t#1), #1) • #0)
  ),

  -- instance fdEqual2 = Λ t t' u. λ i1 i2.
  --     guard EqualTT[t, u] <- i1 then λ c1 : t ~ u.
  --     guard EqualTT[t', u] <- i2 then λ c0 : t' ~ u.
  --         c1 ; sym c0
  .inst "fdBwk"
    #(⟨"EqualTT", 2, #(t#2, t#0), 0, 1⟩,
      ⟨"EqualTT", 2, #(t#1, t#0), 0, 1⟩)
     (((((.defn "seq" •[t#2]) •[t#0]) •[t#1]) • #1) • (((.defn "sym" •[t#1]) •[t#0]) • #0)) ,

  -- instance fdEqual1 = Λ t u u'. λ i1 i0.
  --     guard EqualTT[t, u] <- i1 then λ c1 : t ~ u.
  --     guard EqualTT[t, u'] <- i0 then λ c0 : t ~ u'.
  --         sym c1 ; c0
  .inst "fdFwd"
    #(⟨"EqualTT", 2, #(t#2, t#1), 0, 1⟩,
      ⟨"EqualTT", 2, #(t#2, t#0), 0, 1⟩)
     (((((.defn "seq" •[t#1]) •[t#2]) •[t#0]) • (((.defn "sym" •[t#2]) •[t#1]) • #1)) • #0) ,



  -- instance EqualTT :: ∀ t u. t ~ u -> Equal t u
  .octor "EqualTT" ⟨2, #(★, ★), 0, #(), 1, #(t#1 ~[★]~ t#0), ((gt#"Equal" • t#1) • t#0)⟩,

  -- open fdBwk :: ∀ t t' u. Equal t u -> Equal t' u -> t ~ t'
  .openm "fdBwk" ⟨3, #(★, ★, ★), 0, #(), 2, #(((gt#"Equal" • t#2) • t#0),  ((gt#"Equal" • t#1) • t#0)), (t#2 ~[★]~ t#1)⟩,

  -- open fdFwd :: ∀ t u u'. Equal t u -> Equal t u' -> u ~ u'
  .openm "fdFwd" ⟨3, #(★, ★, ★), 0, #(), 2, #(((gt#"Equal" • t#2) • t#1),  ((gt#"Equal" • t#2) • t#0)), (t#1 ~[★]~ t#0)⟩,

  .odata "Equal" (★ -:> ★ -:> ★)

] ++ Examples.CastCtx

#guard GlobalEnv.wf_globals FunDepsCtx == .some ()
#guard FunDepsCtx.check_open_exhaustive == some ()

-- #eval! do
--   let i := inst! "EqualTT" #(t#1, t#1) #() #(refl! t#1).to
--   let t0 := openm! "fdFwd" #(t#1, t#1, t#0) #() #(i, #1).to
--   (Λ[★]Λ[★]λ[(gt#"Equal" • t#1) • t#0]λ[t#1] Term.cast t#0 t0 #0).infer_type FunDepsCtx [] []

-- #eval! do
--   match lookup "fdFwd" FunDepsCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "fdFwd" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, ξ) <- pattern_binders FunDepsCtx Δ n Ts
--                                #(⟨"EqualTT", 2, #(t#2, t#1), 0, 1⟩, ⟨"EqualTT", 2, #(t#2, t#0), 0, 1⟩)
--         let t := (((((.defn "seq" •[t#1]) •[t#2]) •[t#0]) • (((.defn "sym" •[t#2]) •[t#1]) • #1)) • #0)
--         let R' <- t.infer_type FunDepsCtx (ζ ++ Δ) ξ
--         return (R, R')

--       else none
--       -- let T <- t.infer_type G Ks.to_list Γ
--       -- if T == R then return () else none
--   | _ => none


-- #eval! do
--   match lookup "fdBwk" FunDepsCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "fdBwk" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, ξ) <- pattern_binders FunDepsCtx Δ n Ts
--                           #(⟨"EqualTT", 2, #(t#2, t#0), 0, 1⟩,
--                             ⟨"EqualTT", 2, #(t#1, t#0), 0, 1⟩)
--         let t := (((((.defn "seq" •[t#2]) •[t#0]) •[t#1]) • #1) • (((.defn "sym" •[t#1]) •[t#0]) • #0))

--         let R' <- t.infer_type FunDepsCtx (ζ ++ Δ) ξ
--         return (R, R')

--       else none
--       -- let T <- t.infer_type G Ks.to_list Γ
--       -- if T == R then return () else none
--   | _ => none




end Core.Examples
