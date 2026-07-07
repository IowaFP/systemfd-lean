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

namespace Core.Examples


def ZeroCtor : Term := ctor! "Zero" #() #() .nil
def OneCtor : Term := ctor! "Succ" #() #() #(ZeroCtor).to

def iEqInt : Term := inst! "EqInt" #(gt#"Int") #() #(refl! gt#"Int").to



def MRCtx : GlobalEnv := [



  -- -- BoolBoolFun : ∀ r s. r ~ Bool, s ~ (->) Bool => MonadReader r s
  -- .octor "BoolBoolFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Bool", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Bool")), (gt#"MonadReader" • t#1) • t#0⟩,
  -- -- IntIntFun : ∀ r s. r ~ Int, s ~ (->) Int => MonadReader r s
  -- .octor "IntIntFun" ⟨2, #(★, ★ -:> ★), 0, #(), 2, #(t#1 ~[★]~ gt#"Int", t#0 ~[★ -:> ★]~ (gt#"->" • gt#"Int")), (gt#"MonadReader" • t#1) • t#0⟩,


  -- ∀ r s m. MonadReader r m, MonadReader s m ⇒ r -> s
  .openm "mrDep" ⟨3, #(★, ★, ★ -:> ★), 0, #(), 2, #((gt#"MonadReader" • t#2) • t#0, (gt#"MonadReader" • t#1) • t#0), t#2 ~[★]~ t#1⟩,

  .odata "MonadReader" (★ -:> ((★ -:> ★) -:> ★)),

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



#guard MRCtx.wf_globals == some ()
#guard MRCtx.check_open_exhaustive == some ()
