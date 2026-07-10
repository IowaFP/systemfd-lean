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

namespace Core.Examples.MonadReaderCtxRelation


def MRCtx : GlobalEnv := [

  -- instance toM FstPairFun PairPairFun = λ x r. Pair x snd r
  .inst "toM" #(⟨"FstPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#4]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
        let t2 := (prj[1] t1)
        let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
        let t7 := (d#"seq").mkApps [t#6, t#3, t#1] [#5, t4]
        let t6 :=
            (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, (gt#"Pair" • t#1) • t#0]
               [λ[(gt#"Pair" • t#1) • t#0] (d#"mkPair").mkApps [t#1, t#0] [ Term.cast t#0 t7 #1, (d#"snd").mkApps [t#1, t#0] [#0] ]]
        let t8 := (d#"sym").mkApps [t#4 • t#5, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • ((gt#"Pair" • t#1) • t#0)]
            [(d#"appc").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#5, ((gt#"Pair" • t#1) • t#0)] [#1, #2]]
        λ[t#6] Term.cast t#0 t8 t6
   ),

  -- instance toM PairPairFun FstPairFun = λ x r. fst x
  .inst "toM" #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"FstPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1] [λ[(gt#"Pair" • t#1) • t#0] (d#"fst").mkApps [t#1, t#0] [#0]]
        let t1 := (d#"sym").mkApps [t#4 • t#5, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [(d#"appc").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#5, t#1] [#1, #2]]

        λ[t#6] Term.cast t#0 t1 t0
   ),

  -- instance toM FstPairFun FstPairFun = λ x r. x
  .inst "toM" #(⟨"FstPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"FstPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#4]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
        let t2 := (prj[1] t1)
        let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
        let t6 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1]
                              [λ[(gt#"Pair" • t#1) • t#0] ((Term.cast t#0 t4 (Term.cast t#0 #5 #1)))]
        let t8 := (d#"sym").mkApps [t#4 • t#5, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [(d#"appc").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#5, t#1] [#1, #2]]


        λ[t#6] Term.cast t#0 t8 t6
   ),

  -- instance toM PairPairFun PairPairFun = λ x r. x
  .inst "toM" #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#4]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
        let t2 := (prj[1] t1)
        let t3 := prj[1] t2
        let t4 := prj[1] (prj[0]t2)
        let t5 := Term.cast ((gt#"Pair" • t#2) • t#0) t3 $ Term.cast ((gt#"Pair" • t#0) • t#3) t4 (Term.cast t#0 #5 #1)
        let t6 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, (gt#"Pair" • t#1) • t#0] [λ[(gt#"Pair" • t#1) • t#0] t5]
        let t7 := (d#"sym").mkApps [t#4 • t#5, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • ((gt#"Pair" • t#1) • t#0)] [(d#"appc").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#5, ((gt#"Pair" • t#1) • t#0)] [#1, #2]]
        λ[t#6] Term.cast t#0 t7 t6
   ),

  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r -> m s
  .openm "toM" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 -:> (t#0 • t#1)⟩,


  -- instance ask PairPairFun = λ x. x
  .inst "ask" #(⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
     let t0 := (d#"sym2").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [#0]
     let t1 := (d#"sym").mkApps [t#3, ((gt#"Pair" • t#1) • t#0)] [#1]
     let t3 := (d#"slam").mkApps [((gt#"Pair" • t#1) • t#0), ((gt#"Pair" • t#1) • t#0)] [(λ[((gt#"Pair" • t#1) • t#0)] #0)]
     let t4 := (d#"appc").mkApps [gt#"->" • ((gt#"Pair" • t#1) • t#0), t#2, ((gt#"Pair" • t#1) • t#0), t#3] [t0, t1]
     Term.cast t#0 t4 t3
  ),

  -- PairPairFun : ∀ r s. ∀ t u -> (r ~ Pair t u), (s ~ -> (Pair t u)) => MonadReader r s
  .octor "PairPairFun" ⟨2, #(★, ★ -:> ★), 2, #(★, ★), 2, #(t#3 ~[★]~ ((gt#"Pair" • t#1) • t#0), t#2 ~[★ -:> ★]~ (gt#"->" • ((gt#"Pair" • t#1) • t#0))), (gt#"MonadReader" • t#3) • t#2 ⟩,

  -- instance ask Fstpair Fun = λ x. fst x
  .inst "ask" #(⟨"FstPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t1 := (d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, t#1] [#0, #1]
        let t2 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [t1]
        let t3 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1] [λ[(gt#"Pair" • t#1) • t#0] (d#"fst").mkApps [t#1, t#0] [#0]]
        Term.cast t#0 t2 t3
  ),

  -- FstPairFun : ∀ r s. ∀ t u -> (r ~ t), (s ~ -> (Pair t u)) => MonadReader r s
  .octor "FstPairFun" ⟨2, #(★, ★ -:> ★), 2, #(★, ★), 2, #(t#3 ~[★]~ t#1, t#2 ~[★ -:> ★]~ (gt#"->" • ((gt#"Pair" • t#1) • t#0))), (gt#"MonadReader" • t#3) • t#2 ⟩,

  .openm "ask" ⟨2, #(★, ★ -:> ★), 0, #(), 1, #((gt#"MonadReader" • t#1) • t#0), t#0 • t#1⟩,
  .odata "MonadReader" (★ -:> ((★ -:> ★) -:> ★)),

  .defn "slam" (∀[★]∀[★] (t#1 -:> t#0) -:> ((gt#"->" • t#1) • t#0)) (Λ[★]Λ[★]λ[t#1 -:> t#0] ctor! "lam" #(t#1, t#0) #() #(#0).to),

  .data 1 "->" (★ -:> (★ -:> ★))
    #( ⟨"lam", 2, #(★, ★), 0, #(), 1, #(t#1 -:> t#0), (gt#"->" • t#1) • t#0⟩ ),


] ++ PCtx ++ EqBoolCtx ++ CastCtx

-- #eval! do
--   match lookup "toM" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "toM" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"FstPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩)

--         let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#4]
--         let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
--         let t2 := (prj[1] t1)
--         let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
--         let t7 := (d#"seq").mkApps [t#6, t#3, t#1] [#5, t4]
--         let t6 :=
--             (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, (gt#"Pair" • t#1) • t#0]
--                [λ[(gt#"Pair" • t#1) • t#0] (d#"mkPair").mkApps [t#1, t#0] [ Term.cast t#0 t7 #1, (d#"snd").mkApps [t#1, t#0] [#0] ]]
--         let t8 := (d#"sym").mkApps [t#4 • t#5, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • ((gt#"Pair" • t#1) • t#0)]
--             [(d#"appc").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#5, ((gt#"Pair" • t#1) • t#0)] [#1, #2]]


--         let R' := (λ[t#6] Term.cast t#0 t8 t6).infer_type MRCtx (ζ ++ Δ) Γ

--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none

-- #eval! do
--   match lookup "ask" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "ask" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"FirstPairFun", 2, #(t#1, t#0), 2, 2⟩)
--         let t1 := (d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, t#1] [#0, #1]
--         let t2 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [t1]
--         let t3 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1] [λ[(gt#"Pair" • t#1) • t#0] (d#"fst").mkApps [t#1, t#0] [#0]]
--         let R' := (Term.cast t#0 t2 t3).infer_type MRCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
--       else none
--   | _ => none

-- #eval! do
--   match lookup "absurd" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, m, Ts, R⟩) =>
--       if "absurd" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζΓ) := pattern_binders (.data .opn) MRCtx Δ m Ts #()
--         -- let t1 := (d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, t#1] [#0, #1]
--         -- let t2 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [t1]
--         -- let t3 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1] [λ[(gt#"Pair" • t#1) • t#0] (d#"fst").mkApps [t#1, t#0] [#0]]
--         -- let R' := (Term.cast t#0 t2 t3).infer_type MRCtx (ζ ++ Δ) Γ
--         return Δ -- R'
--       else none
--   | _ => none


#guard MRCtx.wf_globals == some ()
#guard MRCtx.check_open_exhaustive == some ()



end Core.Examples.MonadReaderCtxRelation
