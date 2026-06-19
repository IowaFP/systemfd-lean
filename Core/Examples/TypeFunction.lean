import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Infer.Global
import Core.Examples.Common
import Core.Examples.Maybe

namespace Core.Examples

def TypeFunCtx : GlobalEnv := [
  --    -- not : Bool → Bool → Bool = λ x if x ← True then False else True
  --   .term (#12 -t> #13)
  --          (`λ[#12] Term.ite #11 #0 #12 #11),

  --   Λ t u v. λ d1 d2.
  --     If FMM[t][u] ← d1 then Λ a' b'. λ (h1: Maybe a' ~  t) (h2 : Maybe b' ~ u) (e1 : F a' b').
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ (k1: Maybe a'' ~ t) (k2 : Maybe b'' ~ v) (e2 : F a'' b'').
  --     let j : (a' ~ a'') = (h1 ; sym k1).2
  --     let e1' : F a'' b' = e1 ▹ <F> `@c[ j ] `@c[<b'>]
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] e1' e2 ; k2


  -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  .octor "FMM" ⟨4 , #(★, ★, ★, ★), 0, #(), 3,
             #((gt#"Maybe" • t#1) ~[★]~ t#3,
               (gt#"Maybe" • t#0) ~[★]~ t#2,
               (gt#"F" • t#1) • t#0),
             ((gt#"F" • t#3) • t#2)⟩,

  -- fdf : Λ t u v. λ (d1 : F t u)  (d2 : F t v).
  --       If FIB[t][u] ← d1 then λ (h1: Int ~ t) (h2 : Bool ~ u)
  --       If FIB[t][v] ← d2 then λ (k1: Int ~ t) (k2 : Bool ~ v)
  --          (sym h2) ; k2
  .inst "fdF"
        #(⟨"FIB", 2, #(t#2, t#1), 0, 2⟩, ⟨"FIB", 2, #(t#2, t#0), 0, 2⟩)
        (let t := ((d#"sym" •[gt#"Bool"]) •[t#1]) • #2
         ((((d#"seq" •[t#1]) •[gt#"Bool"]) •[t#0]) • t) • #0),

  -- FIB : ∀ t u. Int ~ t → Bool ~ u → F t u
  .octor "FIB" ⟨2, #(★, ★), 0, #(), 2, #(gt#"Int" ~[★]~ t#1, gt#"Bool" ~[★]~ t#0), (gt#"F" • t#1) • t#0 ⟩,

  -- open fdF : ∀ t u v. F t u → F t v → u ~ v
  .openm "fdF" ⟨3, #(★,★,★), 0, #(), 2, #( ((gt#"F" • t#2) • t#1), ((gt#"F" • t#2) • t#0)), t#1 ~[★]~ t#0⟩,

  -- F : ★ → ★ → ★
  .odata "F" (★ -:> (★ -:> ★)),

  .data 0 "Int" ★ #()   -- Int : ★
  ] ++ MaybeBoolCtx


#guard TypeFunCtx.wf_globals == some ()

#eval! do
  match lookup "fdF" TypeFunCtx with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
      -- Ks1 := #(★, ★) Ks2 := () Ts := [F t u, F t v] R := u ~ v
      if "fdF" == y then
        let Δ := (Ks1.list ++ Ks2.list).reverse
        let (ζ, Γ) <- pattern_binders TypeFunCtx Δ n Ts #(⟨"FMM", 2, #(t#2, t#1), 2, 3⟩, ⟨"FMM", 2, #(t#2, t#0), 2, 3⟩)
        let t := #5
        let R' <- t.infer_type MaybeBoolCtx (ζ ++ Δ) Γ
        return (ζ++Δ, Γ)

      else none
  | _ => none



-- #eval! do
--   match lookup "fdF" TypeFunCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "fdF" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders TypeFunCtx Δ n Ts
--             #(⟨"FIB", 2, #(t#2, t#1), 0, 2⟩, ⟨"FIB", 2, #(t#2, t#0), 0, 2⟩)
--         let t := ((d#"sym" •[gt#"Bool"]) •[t#1]) • #2
--         let t1 := ((((d#"seq" •[t#1]) •[gt#"Bool"]) •[t#0]) • t) • #0
--         let R' <- t1.infer_type MaybeBoolCtx (ζ ++ Δ) Γ
--         return (ζ, Γ, R')

--       else none
--   | _ => none



end Core.Examples
