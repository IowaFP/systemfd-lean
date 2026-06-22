import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Infer.Global
import Core.Examples.Common
import Core.Examples.Maybe

namespace Core.Examples

def TypeFunCtx : GlobalEnv := [

  --   Λ t u v. λ d1 d2.
  --     If FMM[t][u] ← d1 then Λ a' b'. λ (h1: Maybe a' ~  t) (h2 : Maybe b' ~ u) (e1 : F a' b').
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ (k1: Maybe a'' ~ t) (k2 : Maybe b'' ~ v) (e2 : F a'' b'').
  --     let j : (a' ~ a'') = (h1 ; sym k1).2
  --     let e1' : F a'' b' = e1 ▹ <F> `@c[ j ] `@c[<b'>]
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] e1' e2 ; k2


  -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  .octor "FMM" ⟨2 , #(★, ★), 2, #(★, ★),
          3, #((gt#"Maybe" • t#1) ~[★]~ t#3, (gt#"Maybe" • t#0) ~[★]~ t#2, (gt#"F" • t#1) • t#0),
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


-- #guard TypeFunCtx.wf_globals == some ()

  -- -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  -- .octor "FMM" ⟨2 , #(★, ★), 2, #(★, ★),
  --         3, #((gt#"Maybe" • t#1) ~[★]~ t#3, (gt#"Maybe" • t#0) ~[★]~ t#2, (gt#"F" • t#1) • t#0),
  --            ((gt#"F" • t#3) • t#2)⟩,

--some ([], [gt#F • t#3 • t#2, gt#F • t#2 • t#1, gt#F • t#4 • t#3, gt#F • t#4 • t#3])
#eval!
  pattern_binders TypeFunCtx
  /- v  u  t           F       t      u       F        t      v   -/
    [★, ★, ★] 2 #( ((gt#"F" • t#2) • t#1), ((gt#"F" • t#2) • t#0))
  /-                t    u                         t    v           -/
    #(⟨"FMM", 2, #(t#2, t#1), 2, 3⟩, ⟨"FMM", 2, #(t#2, t#0), 2, 3⟩)
  /-  0    1    2    3   4  5  6       0           1             2         3           4             5     -/
  /- b'1  a'1  b'2  a'2  v  u  t     F 1 0   Maybe 0 ~ 4   Maybe 1 ~ 6   F 3 2   Maybe 2 ~ 5   Maybe 3 ~ 6 -/
/-
some ([★, ★, ★, ★],
 [gt#F • t#3 • t#2,
  (gt#Maybe • t#2) ~[★]~ t#4,
  (gt#Maybe • t#3) ~[★]~ t#6,
  gt#F • t#3 • t#2,
  (gt#Maybe • t#2) ~[★]~ t#5,
  (gt#Maybe • t#3) ~[★]~ t#6])
-/

#eval! do
  match lookup "fdF" TypeFunCtx with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
      -- Ks1 := #(★, ★, ★) Ks2 := #() Ts := [F t u, F t v] R := u ~ v
      if "fdF" == y then
        let Δ := (Ks1.list ++ Ks2.list).reverse
        let (ζ, Γ) <- pattern_binders TypeFunCtx Δ n Ts #(⟨"FMM", 2, #(t#2, t#1), 2, 3⟩, ⟨"FMM", 2, #(t#2, t#0), 2, 3⟩)
        let t := #5
        let R' <- t.infer_type MaybeBoolCtx (ζ ++ Δ) Γ
        return (ζ++Δ, Γ)

      else none
  | _ => none


/-
some ([★, ★, ★, ★, ★, ★, ★],
 [gt#F • t#1 • t#0,
  (gt#Maybe • t#0) ~[★]~ t#2, -- Expected (gt#Maybe • t#0) ~[★]~ t#4
  (gt#Maybe • t#1) ~[★]~ t#4, -- Exptected (gt#Maybe • t#1) ~[★]~ t#6
  gt#F • t#3 • t#2,
  (gt#Maybe • t#2) ~[★]~ t#5,
  (gt#Maybe • t#3) ~[★]~ t#6])
-/

/-
some ([★, ★, ★, ★, ★, ★, ★],
 [gt#F • t#1 • t#0,
  (gt#Maybe • t#0) ~[★]~ t#2,
  (gt#Maybe • t#1) ~[★]~ t#4,
  gt#F • t#1 • t#0,
  (gt#Maybe • t#0) ~[★]~ t#3,
  (gt#Maybe • t#1) ~[★]~ t#4])
-/

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


-- f : ∀ t. F Int t → t → t
--   = Λ t λ (d : F Int t).
--     let h : Bool ~ t = fdF[Int][Bool][t](FIB [Int][Bool] <Int> <Bool>) d in
--     not ▹ <→> `@c h `@c h
-- def fnot := Λ[★]`λ[#10 `@k #11 `@k #0]
--         .letterm ((#15 ~[★]~ #1))
--           (#10 `@t #12 `@t #15 `@t #1
--                `@ (#9 `@t #12 `@t #15 `@ (refl! ★ #12) `@ (refl! ★ #15))
--                `@ #0)
--             (#3 ▹ (#0 -c> #1))



end Core.Examples
