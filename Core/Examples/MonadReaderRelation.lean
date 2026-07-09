import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Kind
import Core.Typing

import Core.Examples.Common
import Core.Examples.Boolean
import Core.Examples.Pairs

open LeanSubst

namespace Core.Examples.MonadReaderRelation

def MRCtx : GlobalEnv := [


  .inst "to" #(⟨"FlipPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#3]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #1]
        let t2 := (prj[1] t1)
        let t3 := (d#"sym").mkApps [t#5, ((gt#"Pair" • t#1) • t#0)] [#2]
        let t4 := Term.cast t#0 t2 ((d#"flipPair").mkApps [t#2, t#3] [Term.cast t#0 #4 #0])
        λ[t#6] Term.cast t#0 t3 t4
  ),

  .inst "to" #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"FlipPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#3]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #1]
        let t2 := (prj[1] t1)
        let t3 := (d#"sym").mkApps [t#5, ((gt#"Pair" • t#0) • t#1)] [#2]
        let t4 := (d#"flipPair").mkApps [t#1, t#0] [Term.cast t#0 t2 (Term.cast t#0 #4 #0)]
        λ[t#6] Term.cast t#0 t3 t4
  ),

  .inst "to" #(⟨"FlipPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"FlipPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#3]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #1]
        let t2 := (prj[1] t1)
        let t3 := prj[1] t2
        let t4 := prj[1] (prj[0]t2)
        let t5 := Term.cast ((gt#"Pair" • t#1) • t#0) t4 (Term.cast ((gt#"Pair" • t#0) • t#4) t3 (Term.cast t#0 #4 #0))
        let t6 := (d#"sym").mkApps [t#5, ((gt#"Pair" • t#0) • t#1)] [#2]
        λ[t#6] Term.cast t#0 t6 t5
  ),


  .inst "to" #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#3]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #1]
        let t2 := (prj[1] t1)
        let t3 := (d#"sym").mkApps [t#5, ((gt#"Pair" • t#1) • t#0)] [#2]
        let t4 := (d#"seq").mkApps [t#6, ((gt#"Pair" • t#3) • t#2), ((gt#"Pair" • t#1) • t#0)] [#4, t2]
        let t5 := (d#"seq").mkApps [t#6, ((gt#"Pair" • t#1) • t#0), t#5] [t4, t3]
        λ[t#6] Term.cast t#0 t5 #0
  ),

  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r -> s
  .openm "to" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 -:> t#1⟩,

  .inst "ask" #(⟨"FlipPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [#0]
        let t1 := (d#"sym").mkApps [t#3, ((gt#"Pair" • t#0) • t#1)] [#1]
        let t3 := (d#"slam").mkApps [((gt#"Pair" • t#1) • t#0), ((gt#"Pair" • t#0) • t#1)] [(λ[((gt#"Pair" • t#1) • t#0)] ((d#"flipPair").mkApps [t#1, t#0] [#0]))]
        let t4 := (d#"appc").mkApps [gt#"->" • ((gt#"Pair" • t#1) • t#0), t#2, ((gt#"Pair" • t#0) • t#1), t#3] [t0, t1]
        (Term.cast t#0 t4 t3)
   ),

  -- FlipPairFun : ∀ r s. ∀ t u -> (r ~ Pair u t), (s ~ -> (Pair t u)) => MonadReader r s
  .octor "FlipPairFun" ⟨2, #(★, ★ -:> ★), 2, #(★, ★), 2, #(t#3 ~[★]~ ((gt#"Pair" • t#0) • t#1), t#2 ~[★ -:> ★]~ (gt#"->" • ((gt#"Pair" • t#1) • t#0))), (gt#"MonadReader" • t#3) • t#2 ⟩,

  .inst "ask" #(⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
     let t0 := (d#"sym2").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [#0]
     let t1 := (d#"sym").mkApps [t#3, ((gt#"Pair" • t#1) • t#0)] [#1]
     let t3 := (d#"slam").mkApps [((gt#"Pair" • t#1) • t#0), ((gt#"Pair" • t#1) • t#0)] [(λ[((gt#"Pair" • t#1) • t#0)] #0)]
     let t4 := (d#"appc").mkApps [gt#"->" • ((gt#"Pair" • t#1) • t#0), t#2, ((gt#"Pair" • t#1) • t#0), t#3] [t0, t1]
     Term.cast t#0 t4 t3
  ),

  -- PairPairFun : ∀ r s. ∀ t u -> (r ~ Pair t u), (s ~ -> (Pair t u)) => MonadReader r s
  .octor "PairPairFun" ⟨2, #(★, ★ -:> ★), 2, #(★, ★), 2, #(t#3 ~[★]~ ((gt#"Pair" • t#1) • t#0), t#2 ~[★ -:> ★]~ (gt#"->" • ((gt#"Pair" • t#1) • t#0))), (gt#"MonadReader" • t#3) • t#2 ⟩,


  .openm "ask" ⟨2, #(★, ★ -:> ★), 0, #(), 1, #((gt#"MonadReader" • t#1) • t#0), t#0 • t#1⟩,
  .odata "MonadReader" (★ -:> ((★ -:> ★) -:> ★)),

  .defn "slam" (∀[★]∀[★] (t#1 -:> t#0) -:> ((gt#"->" • t#1) • t#0)) (Λ[★]Λ[★]λ[t#1 -:> t#0] ctor! "lam" #(t#1, t#0) #() #(#0).to),

  .data 1 "->" (★ -:> (★ -:> ★))
    #( ⟨"lam", 2, #(★, ★), 0, #(), 1, #(t#1 -:> t#0), (gt#"->" • t#1) • t#0⟩ ),

] ++ PCtx ++ EqBoolCtx ++ CastCtx

-- #eval! do
--   match lookup "to" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "to" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         -- let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"FlipPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"FlipPairFun", 2, #(t#1, t#0), 2, 2⟩)

--         let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#3]
--         let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #1]
--         let t2 := (prj[1] t1)
--         let t3 := prj[1] t2
--         let t4 := prj[1] (prj[0]t2)
--         let t5 := Term.cast ((gt#"Pair" • t#1) • t#0) t4 (Term.cast ((gt#"Pair" • t#0) • t#4) t3 (Term.cast t#0 #4 #0))
--         let t6 := (d#"sym").mkApps [t#5, ((gt#"Pair" • t#0) • t#1)] [#2]
--         let R' := (λ[t#6] Term.cast t#0 t6 t5).infer_type MRCtx (ζ ++ Δ) Γ

--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none



-- #eval! do
--   match lookup "eq" MPCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "eq" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"EqInt", 1, #(t#0), 0, 1⟩)

--         let R' := (λ[t#0]λ[t#0]λ[gt#"Int"]λ[gt#"Int"] inst! "EqInt" #(gt#"Int") #() #(refl! gt#"Int").to ).infer_type MPCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
--       else none
--   | _ => none


#guard MRCtx.wf_globals == some ()
#guard MRCtx.check_open_exhaustive == some ()



end Core.Examples.MonadReaderRelation
