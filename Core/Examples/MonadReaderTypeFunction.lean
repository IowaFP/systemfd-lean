import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer.Kind
import Core.Typing

import Core.Examples.Common
import Core.Examples.Boolean

open LeanSubst

namespace Core.Examples.MonadReaderTypeFunction


def ZeroCtor : Term := ctor! "Zero" #() #() .nil
def OneCtor : Term := ctor! "Succ" #() #() #(ZeroCtor).to

def iEqInt : Term := inst! "EqInt" #(gt#"Int") #() #(refl! gt#"Int").to


def MRCtx : GlobalEnv := [

  .inst "mrDep" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩) (
    openm! "loop" #(t#2 ~[★]~ t#1) #() #().to
  ),

  .inst "mrDep" #(⟨"BoolBoolFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
    openm! "loop" #(t#2 ~[★]~ t#1) #() #().to
  ),


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

  .inst "mrDep" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"sym").mkApps [t#1, gt#"Int"] [#1]
        let t0 := (d#"seq").mkApps [t#2, gt#"Int", gt#"Int"] [#3, refl! gt#"Int"]
        (d#"seq").mkApps [t#2, gt#"Int", t#1] [t0, t1]

  ),

  .inst "return" #(⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [λ[gt#"Int"] Term.cast t#0 #3 #1 ]
        λ[t#1] Term.cast t#0 t2 t3
   ),

  -- IntIntFun : ∀ r s. r ~ Int, s ~ (->) Int => MonadReader r s
  .octor "IntIntFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Int", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Int")), (gt#"MonadReader" • t#1) • t#0⟩,

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

] ++ EqBoolCtx ++ CastCtx


-- #eval! do
--   match lookup "return" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "return" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         -- let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#1, #2]
--         let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
--         let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [λ[gt#"Int"] Term.cast t#0 #3 #1 ]
--         -- let t4 := (d#"arrowc").mkApps [t#1, t#1, (gt#"->" • gt#"Int") • gt#"Int" , t#0 • t#1] [refl! t#1, t2]
--         -- let R' := (λ[t#1] t4).infer_type MRCtx (ζ ++ Δ) Γ
--         let R' := (λ[t#1] Term.cast t#0 t2 t3).infer_type MRCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none


-- #eval! do
--   match lookup "mrDep" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "mrDep" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         -- let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"BoolBoolFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolBoolFun", 2, #(t#1, t#0), 0, 2⟩)
--         let t1 := (d#"sym").mkApps [t#1, gt#"Bool"] [#1]
--         let t0 := (d#"seq").mkApps [t#2, gt#"Bool", gt#"Bool"] [#3, refl! gt#"Bool"]
--         let t2 := (d#"seq").mkApps [t#2, gt#"Bool", t#1] [t0, t1]
--         let R' := (t2).infer_type MRCtx (ζ ++ Δ) Γ

--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R')
--       else none
--   | _ => none

def fdTy : Ty := ∀[★]∀[★]∀[★ -:> ★] (gt#"MonadReader" • t#2) • t#0 -:> (((gt#"MonadReader" • t#1) • t#0) -:> (t#2 -:> (t#0 • t#1)))

def fdTerm : Term := Λ[★]Λ[★]Λ[★ -:> ★]λ[(gt#"MonadReader" • t#2) • t#0]λ[(gt#"MonadReader" • t#1) • t#0]λ[t#2] (
  let t1 := openm! "mrDep" #(t#2, t#1, t#0) #() #(#2, #1).to
  let t2 := (d#"appc").mkApps [t#0, t#0, t#2, t#1] [refl! t#0, t1]
  Term.cast t#0 t2 ((openm! "return" #(t#2, t#0) #() #(#2).to).mkApps [] [#0])
 )


#eval fdTerm.infer_type MRCtx [] []
-- #guard fdTerm.infer_type MRCtx [] [] == some fdTy


#guard MRCtx.wf_globals == some ()
#guard MRCtx.check_open_exhaustive == some ()

end Core.Examples.MonadReaderTypeFunction
