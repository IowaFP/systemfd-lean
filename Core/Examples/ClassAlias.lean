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

namespace Core.Examples.ClassAlias

def CACtx : GlobalEnv := [

  .inst "mpRequirement" #(⟨"ListMon", 1, #(t#0), 0, 1⟩, ⟨"ListAlt", 1, #(t#0), 0, 1⟩) (inst! "ListMonPlus" #(t#0) #() #(#0).to),
  .octor "ListMonPlus" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"List"), gt#"MonadPlus" • t#0⟩,
  .octor "ListAlt" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"List"), gt#"Alternative" • t#0⟩,
  .octor "ListMon" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"List"), gt#"Monad" • t#0⟩,

  -- List ★ → ★ where
  --   Nil : ∀ α. List α
  --   Cons : ∀ α. α → List α → List α
  .data 2 "List" (★ -:> ★)
      #( ("Nil", ⟨1, #(★), 0, #(), 0, #(), (gt#"List" • t#0)⟩),
         ("Cons", ⟨1, #(★), 0, #(), 2,  #(t#0, gt#"List" • t#0), (gt#"List" • t#0)⟩) ),

  -- mpRequirement : ∀ t. Monad t, Alternative t ⇒ MonadPlus t
  .openm "mpRequirement" ⟨1, #(★ -:> ★), 0, #(), 2, #(gt#"Monad" • t#0, gt#"Alternative" • t#0), gt#"MonadPlus" • t#0⟩,
  -- class MonadPlus (m : ★ → ★)
  .odata "MonadPlus" ((★ -:> ★) -:> ★),
  -- class Alternative (m : ★ → ★)
  .odata "Alternative" ((★ -:> ★) -:> ★),
  -- class Monad (m : ★ → ★)
  .odata "Monad" ((★ -:> ★) -:> ★) ] ++ CastCtx


#guard CACtx.wf_globals == some ()
#guard CACtx.check_open_exhaustive == some ()

end Core.Examples.ClassAlias
