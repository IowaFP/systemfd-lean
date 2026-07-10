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

namespace Core.Examples.MonadReaderTypeFunction

def MRCtx : GlobalEnv := [

  .inst "mrDep"  #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#2, gt#"->" • (gt#"Bool")] [#0]
        let t1 := (d#"seq2").mkApps [gt#"->" • gt#"Bool", t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
        let t2 := (prj[1] t1)
        let t3 := (d#"sym").mkApps [gt#"Bool", ((gt#"Pair" • t#1) • t#0)] [t2]
        (openm! "absurd" #() #() #().to).mkApps [t#1, t#0, t#4, t#3] [t3]
  ),

  .inst "mrDep" #(⟨"BoolBoolFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [#0]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#1) • t#0), t#2, gt#"->" • gt#"Bool"] [t0, #2]
        let t2 := (prj[1] t1)
       (openm! "absurd" #() #() #().to).mkApps [t#1, t#0, t#4, t#3] [t2]
  ),


  .inst "mrDep" #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#2]
        let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #0]
        let t2 := (prj[1] t1)
        let t3 := prj[1] t2   -- 2 ~ 0
        let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
        let t5 := (d#"appc2").mkApps [gt#"Pair", gt#"Pair", t#3, t#1, t#2, t#0] [refl! gt#"Pair", t4, t3]
        let t6 := (d#"sym").mkApps [t#5, (gt#"Pair" • t#1) • t#0] [#1]
        let t7 := (d#"seq").mkApps [t#6, (gt#"Pair" • t#3) • t#2,(gt#"Pair" • t#1) • t#0] [#3, t5]
        (d#"seq").mkApps [t#6,(gt#"Pair" • t#1) • t#0, t#5] [t7, t6]
  ),

  -- instance return PairPairFun = λ x. x
  .inst "return" #(⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩) (
        let t0 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • ((gt#"Pair" • t#1) • t#0)]
            [(d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, ((gt#"Pair" • t#1) • t#0)] [#1, #2]]
        let t1 :=
            (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, (gt#"Pair" • t#1) • t#0]
               [λ[(gt#"Pair" • t#1) • t#0] #0]
        λ[t#3] Term.cast t#0 t0 t1
   ),

  -- PairPairFun : ∀ r s. ∀ t u -> (r ~ Pair t u), (s ~ -> (Pair t u)) => MonadReader r s
  .octor "PairPairFun" ⟨2, #(★, ★ -:> ★), 2, #(★, ★), 2, #(t#3 ~[★]~ ((gt#"Pair" • t#1) • t#0), t#2 ~[★ -:> ★]~ (gt#"->" • ((gt#"Pair" • t#1) • t#0))), (gt#"MonadReader" • t#3) • t#2 ⟩,

  .inst "absurd" #() (Λ[★]Λ[★]Λ[★]Λ[★]λ[((gt#"Pair" • t#3) • t#2) ~[★]~ gt#"Bool"] (openm! "absurd" #() #() #().to).mkApps [t#3, t#2, t#1, t#0] [#0]),
  .openm "absurd" ⟨0, #(), 0, #(), 0, #(), ∀[★]∀[★]∀[★]∀[★](((gt#"Pair" • t#3) • t#2) ~[★]~ gt#"Bool") -:> ((t#1 ~[★]~ t#0))⟩,



  .inst "mrDep" #(⟨"BoolBoolFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"sym").mkApps [t#1, gt#"Bool"] [#1]
        let t0 := (d#"seq").mkApps [t#2, gt#"Bool", gt#"Bool"] [#3, refl! gt#"Bool"]
        (d#"seq").mkApps [t#2, gt#"Bool", t#1] [t0, t1]

  ),

  .inst "return" #(⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Bool", t#1, gt#"Bool"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Bool") • gt#"Bool"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Bool", gt#"Bool"] [λ[gt#"Bool"] Term.cast t#0 #3 #1 ]
        λ[t#1] Term.cast t#0 t2 t3
   ),

  -- BoolBoolFun : ∀ r s. r ~ Bool, s ~ (->) Bool => MonadReader r s
  .octor "BoolBoolFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Bool", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Bool")), (gt#"MonadReader" • t#1) • t#0⟩,


  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r ~ s
  .openm "mrDep" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 ~[★]~ t#1⟩,
  -- return : ∀ r m. MonadReader r m ⇒ r -> m r
  .openm "return" ⟨2, #(★, ★ -:> ★), 0, #(), 1, #((gt#"MonadReader" • t#1) • t#0), t#1 -:> (t#0 • t#1) ⟩,
  .odata "MonadReader" (★ -:> ((★ -:> ★) -:> ★)),



  .defn "slam" (∀[★]∀[★] (t#1 -:> t#0) -:> ((gt#"->" • t#1) • t#0)) (Λ[★]Λ[★]λ[t#1 -:> t#0] ctor! "lam" #(t#1, t#0) #() #(#0).to),
  .data 1 "->" (★ -:> (★ -:> ★))
    #( ⟨"lam", 2, #(★, ★), 0, #(), 1, #(t#1 -:> t#0), (gt#"->" • t#1) • t#0⟩ ),

  .data 2 "Int" ★
    #( ⟨"Zero", 0, #(), 0, #(), 0, #(), gt#"Int"⟩
     , ⟨"Succ", 0, #(), 0, #(), 1, #(gt#"Int"), gt#"Int"⟩
     ),

] ++ PCtx ++ EqBoolCtx ++ CastCtx



def fdTy : Ty := ∀[★]∀[★]∀[★ -:> ★] ((gt#"MonadReader" • t#2) • t#0) -:> (((gt#"MonadReader" • t#1) • t#0) -:> (t#2 -:> (t#0 • t#1)))

def fdTerm : Term := Λ[★]Λ[★]Λ[★ -:> ★]λ[(gt#"MonadReader" • t#2) • t#0]λ[(gt#"MonadReader" • t#1) • t#0]λ[t#2] (
  let t1 := openm! "mrDep" #(t#2, t#1, t#0) #() #(#2, #1).to
  let t2 := (d#"appc").mkApps [t#0, t#0, t#2, t#1] [refl! t#0, t1]
  Term.cast t#0 t2 ((openm! "return" #(t#2, t#0) #() #(#2).to).mkApps [] [#0])
 )

#guard fdTerm.infer_type MRCtx [] [] == some fdTy


#guard MRCtx.wf_globals == some ()
#guard MRCtx.check_open_exhaustive == some ()



-- #eval! do
--   match lookup "return" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "return" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"PairPairFun", 2, #(t#1, t#0), 2, 2⟩)

--         let t0 := (d#"sym2").mkApps [t#4, gt#"->" • ((gt#"Pair" • t#3) • t#2)] [#4]
--         let t1 := (d#"seq2").mkApps [gt#"->" • ((gt#"Pair" • t#3) • t#2), t#4, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
--         let t2 := (prj[1] t1)
--         let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
--         let t7 := (d#"seq").mkApps [t#6, t#3, t#1] [#5, t4]
--         let t8 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • ((gt#"Pair" • t#1) • t#0)]
--             [(d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, ((gt#"Pair" • t#1) • t#0)] [#1, #2]]

--         let t6 :=
--             (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, (gt#"Pair" • t#1) • t#0]
--                [λ[(gt#"Pair" • t#1) • t#0] #0]

--         let R' := (λ[t#3] Term.cast t#0 t8 t6).infer_type MRCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none


-- #eval! do
--   match lookup "mrDep" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "mrDep" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         -- let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"PairPairFun", 2, #(t#2, t#0), 2, 2⟩, ⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩)

--         -- let t1 := (d#"sym2").mkApps [t#0, gt#"->" • gt#"Bool"] [#0]
--         -- let t0 := (d#"seq2").mkApps [gt#"->" • gt#"Bool", t#0, gt#"->" • gt#"Int"] [t1, #2]
--         -- let t2 := (d#"seq").mkApps [t#2, gt#"Bool", t#1] [t0, t1]

--         let t0 := (d#"sym2").mkApps [t#2, gt#"->" • (gt#"Bool")] [#0]
--         let t1 := (d#"seq2").mkApps [gt#"->" • gt#"Bool", t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0)] [t0, #2]
--         let t2 := (prj[1] t1)
--         let t3 := (d#"sym").mkApps [gt#"Bool", ((gt#"Pair" • t#1) • t#0)] [t2]
--         -- let t3 := prj[1] t2   -- 2 ~ 0
--         -- let t4 := prj[1] (prj[0]t2) -- 3 ~ 1
--         -- let t5 := (d#"appc2").mkApps [gt#"Pair", gt#"Pair", t#3, t#1, t#2, t#0] [refl! gt#"Pair", t4, t3]
--         -- let t6 := (d#"sym").mkApps [t#5, (gt#"Pair" • t#1) • t#0] [#1]
--         -- let t7 := (d#"seq").mkApps [t#6, (gt#"Pair" • t#3) • t#2,(gt#"Pair" • t#1) • t#0] [#3, t5]
--         -- (d#"seq").mkApps [t#6,(gt#"Pair" • t#1) • t#0, t#5] [t7, t6]
--         let R' := ((openm! "absurd" #() #() #().to).mkApps [t#1, t#0, t#4, t#3] [t3]).infer_type MRCtx (ζ ++ Δ) Γ

--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none


-- #eval! do
--   match lookup "absurd" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, m, Ts, R⟩) =>
--       if "absurd" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ m Ts #()
--         -- let t1 := (d#"appc").mkApps [t#2, gt#"->" • ((gt#"Pair" • t#1) • t#0), t#3, t#1] [#0, #1]
--         -- let t2 := (d#"sym").mkApps [t#2 • t#3, (gt#"->" • ((gt#"Pair" • t#1) • t#0)) • t#1] [t1]
--         -- let t3 := (d#"slam").mkApps [(gt#"Pair" • t#1) • t#0, t#1] [λ[(gt#"Pair" • t#1) • t#0] (d#"fst").mkApps [t#1, t#0] [#0]]
--         let R' := (Λ[★]Λ[★]Λ[★]Λ[★]λ[((gt#"Pair" • t#3) • t#2) ~[★]~ gt#"Bool"] (openm! "absurd" #() #() #().to).mkApps [t#3, t#2, t#1, t#0] [#0]).infer_type MRCtx (ζ ++ Δ) Γ

--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
--       else none
--   | _ => none


end Core.Examples.MonadReaderTypeFunction
