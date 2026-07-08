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

namespace Core.Examples.MonadReaderRelation


def ZeroCtor : Term := ctor! "Zero" #() #() .nil
def OneCtor : Term := ctor! "Succ" #() #() #(ZeroCtor).to

def iEqInt : Term := inst! "EqInt" #(gt#"Int") #() #(refl! gt#"Int").to

def MRCtx : GlobalEnv := [

  .inst "toM" #(⟨"BoolIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [λ[gt#"Int"] (
            mtch' #(Term.cast t#0 #5 #1, (openm! "eq" #(gt#"Int") #() #(iEqInt).to).mkApps [] [#0, ZeroCtor]) #(
            (#(TruePat, TruePat), ZeroCtor),
            (#(TruePat, FalsePat), ZeroCtor),
            (#(FalsePat, TruePat), OneCtor),
            (#(FalsePat, FalsePat), #0),
            ))]
        λ[t#2] Term.cast t#0 t2 t3
   ),

  .inst "toM" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Bool"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Bool"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Bool"] [(λ[gt#"Int"] (openm! "eq" #(gt#"Int") #() #(iEqInt).to).mkApps [] [#0, ZeroCtor] )]
        λ[t#2] Term.cast t#0 t2 t3
   ),


  .inst "toM" #(⟨"BoolIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Bool"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Bool"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Bool"] [(λ[gt#"Int"] Term.cast t#0 #5 #1)]
        λ[t#2] Term.cast t#0 t2 t3
   ),

  .inst "toM" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#1, #2]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [(λ[gt#"Int"] #0)]
        λ[t#2] Term.cast t#0 t2 t3
   ),

  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r -> m s
  .openm "toM" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 -:> (t#0 • t#1)⟩,


  .inst "to" #(⟨"BoolIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
     let t0 := (d#"sym").mkApps [t#1, gt#"Int"] [#2]
     λ[t#2] Term.cast t#0 t0 (mtch' #(Term.cast t#0 #4 #0)
          #( (#(TruePat), ZeroCtor)
          ,  (#(FalsePat), OneCtor)))
  ),

  .inst "to" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩) (
    let t0 := (d#"sym").mkApps [t#1, gt#"Bool"] [#2]
    (λ[t#2] Term.cast t#0 t0 ((openm! "eq" #(gt#"Int") #() #(iEqInt).to).mkApps [] [Term.cast t#0 #4 #0, ZeroCtor]))
  ),

  .inst "to" #(⟨"BoolIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t0 := (d#"sym").mkApps [t#1, gt#"Bool"] [#2]
        let t1 := (d#"seq").mkApps [t#2, gt#"Bool", t#1] [#4, t0]
        λ[t#2] Term.cast t#0 t1 #0
  ),


  .inst "to" #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t0 := (d#"sym").mkApps [t#1, gt#"Int"] [#2]
        let t1 := (d#"seq").mkApps [t#2, gt#"Int", t#1] [#4, t0]
        λ[t#2] Term.cast t#0 t1 #0
  ),

  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r -> s
  .openm "to" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 -:> t#1⟩,

  .inst "ask" #(⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Bool"] [#0, #1]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Bool"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Bool"] [
            λ[gt#"Int"] (openm! "eq" #(gt#"Int") #() #(inst! "EqInt" #(gt#"Int") #() #(refl! gt#"Int").to).to).mkApps []
                        [#0, ZeroCtor]]
        (Term.cast t#0 t2 t3)
   ),

  .octor "BoolIntFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Bool", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Int")), (gt#"MonadReader" • t#1) • t#0⟩,

  .inst "eq" #(⟨"EqInt", 1, #(t#0), 0, 1⟩) (λ[t#0]λ[t#0]
      mtch' #(Term.cast t#0 #2 #1, Term.cast t#0 #2 #0)
      #( (#(⟨"Zero", 0, #(), 0, 0⟩, ⟨"Zero", 0, #(), 0, 0⟩), TrueCtor)
       , (#(⟨"Zero", 0, #(), 0, 0⟩, ⟨"Succ", 0, #(), 0, 1⟩), FalseCtor)
       , (#(⟨"Succ", 0, #(), 0, 1⟩, ⟨"Zero", 0, #(), 0, 0⟩), FalseCtor)
       , (#(⟨"Succ", 0, #(), 0, 1⟩, ⟨"Succ", 0, #(), 0, 1⟩), (openm! "eq" #(gt#"Int") #() #(iEqInt).to).mkApps [] [#1, #0])
       )
   ),
  .octor "EqInt" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Int"), gt#"Eq" • t#0⟩,


  .inst "ask" #(⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩) (
        let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#0, #1]
        let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
        let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [(λ[gt#"Int"] #0)]
        (Term.cast t#0 t2 t3)
   ),


  -- IntIntFun : ∀ r s. r ~ Int, s ~ (->) Int => MonadReader r s
  .octor "IntIntFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Int", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Int")), (gt#"MonadReader" • t#1) • t#0⟩,


  .defn "slam" (∀[★]∀[★] (t#1 -:> t#0) -:> ((gt#"->" • t#1) • t#0)) (Λ[★]Λ[★]λ[t#1 -:> t#0] ctor! "lam" #(t#1, t#0) #() #(#0).to),

  .data 1 "->" (★ -:> (★ -:> ★))
    #( ⟨"lam", 2, #(★, ★), 0, #(), 1, #(t#1 -:> t#0), (gt#"->" • t#1) • t#0⟩ ),


  .openm "ask" ⟨2, #(★, ★ -:> ★), 0, #(), 1, #((gt#"MonadReader" • t#1) • t#0), t#0 • t#1⟩,
  .odata "MonadReader" (★ -:> ((★ -:> ★) -:> ★)),

  .openm "mpRequirement" ⟨1, #(★ -:> ★), 0, #(), 2, #(gt#"Monad" • t#0, gt#"Alternative" • t#0), gt#"MonadPlus" • t#0⟩,
  -- class MonadPlus (m : ★ → ★)
  .odata "MonadPlus" ((★ -:> ★) -:> ★),
  -- class Alternative (m : ★ → ★)
  .odata "Alternative" ((★ -:> ★) -:> ★),
  -- class Monad (m : ★ → ★)
  .odata "Monad" ((★ -:> ★) -:> ★),

  .data 2 "Int" ★
    #( ⟨"Zero", 0, #(), 0, #(), 0, #(), gt#"Int"⟩
     , ⟨"Succ", 0, #(), 0, #(), 1, #(gt#"Int"), gt#"Int"⟩
     ),

] ++ EqBoolCtx ++ CastCtx

-- #eval! do
--   match lookup "toM" MRCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "toM" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         -- let (ζ, Γ) <- pattern_binders (.data .opn) MPCtx Δ n Ts #(⟨"IntIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"BoolIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let (ζ, Γ) <- pattern_binders (.data .opn) MRCtx Δ n Ts #(⟨"BoolIntFun", 2, #(t#2, t#0), 0, 2⟩, ⟨"IntIntFun", 2, #(t#1, t#0), 0, 2⟩)
--         let t1 := (d#"appc").mkApps [t#0, gt#"->" • gt#"Int", t#1, gt#"Int"] [#1, #2]
--         let t2 := (d#"sym").mkApps [t#0 • t#1, (gt#"->" • gt#"Int") • gt#"Int"] [t1]
--         let t3 := (d#"slam").mkApps [gt#"Int", gt#"Int"] [λ[gt#"Int"] (
--             mtch' #(Term.cast t#0 #5 #1, (openm! "eq" #(gt#"Int") #() #(iEqInt).to).mkApps [] [#0, ZeroCtor]) #(
--             (#(TruePat, TruePat), ZeroCtor),
--             (#(TruePat, FalsePat), ZeroCtor),
--             (#(FalsePat, TruePat), OneCtor),
--             (#(FalsePat, FalsePat), #0),
--             ))]
--         let R' := (λ[t#2] Term.cast t#0 t2 t3
--           ).infer_type MRCtx (ζ ++ Δ) Γ

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
