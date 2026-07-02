import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Infer.Global
import Core.Examples.Common
import Core.Examples.Maybe
open LeanSubst


namespace Core.Examples.AlternativeMonoid

def AMCtx : GlobalEnv := [

  /-
  inst type AltList : Alternative List
  inst monoidal List AltList = MonList
  -/
  .inst "monoidal" #(⟨"AltList", 1, #(t#0), 0, 1⟩) (Λ[★]
        inst! "MonList" #(t#1 • t#0) #(t#0) #((d#"appc").mkApps [t#1, gt#"List", t#0, t#0] [#0, refl! t#0]).to),
  .octor "AltList" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"List"), gt#"Alternative" • t#0 ⟩,

  /-
  open type Alternative : (* -> *) -> *
  open monoidal : forall t. Alternative t -> forall u. Monoid (t u)
  -/
  .openm "monoidal" ⟨1, #(★ -:> ★), 0, #(), 1, #(gt#"Alternative" • t#0),  ∀[★] gt#"Monoid" • (t#1 • t#0)⟩,
  .odata "Alternative" ((★ -:> ★) -:> ★),


  /-
    inst type MonList : forall t u. t ~ List u -> Monoid t
    inst mempty (List t) (MonList t) = []
  -/
  .inst "mempty" #(⟨"MonList", 1, #(t#0), 1, 1⟩) (
        let t1 := ctor! "Nil" #(t#0) .nil .nil
        let t2 := ((d#"sym" •[t#1]) •[gt#"List" • t#0]) • #0
        Term.cast t#0 t2 t1),
  .octor "MonList" ⟨1, #(★), 1, #(★), 1, #(t#1 ~[★]~ (gt#"List" • t#0)), gt#"Monoid" • t#1⟩,

  /-
  class Monoid m where
  mempty :: ∀ m. Monoid m -> m
    (<>) :: ∀ m. Monoid m -> m -> m -> m
  -/
  .openm "mempty" ⟨1, #(★), 0, #(), 1, #(gt#"Monoid" • t#0), t#0⟩ ,
  .odata "Monoid" (★ -:> ★),


  -- List ★ → ★ where
  --   Nil : ∀ α. List α
  --   Cons : ∀ α. α → List α → List α
  .data 2 "List" (★ -:> ★)
      #( ("Nil", ⟨1, #(★), 0, #(), 0, #(), (gt#"List" • t#0)⟩),
         ("Cons", ⟨1, #(★), 0, #(), 2,  #(t#0, gt#"List" • t#0), (gt#"List" • t#0)⟩) )

  ] ++ CastCtx


#guard AMCtx.wf_globals == .some ()
#guard AMCtx.check_open_exhaustive == some ()


end Core.Examples.AlternativeMonoid
