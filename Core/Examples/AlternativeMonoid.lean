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
  instance AltList : Alternative List
  instance altMonoid1 List AltList = MonList
  instance altMonoid2 List AltList = MonList
  -/
  -- .inst "altMonoid2" #(⟨"AltList", 1, #(t#0), 0, 1⟩) (sorry),
  .inst "altMonoid1" #(⟨"AltList", 1, #(t#0), 0, 1⟩) (Λ[★]
        inst! "MonList" #(t#1 • t#0) #(t#0) #((d#"appc").mkApps [t#1, gt#"List", t#0, t#0] [#0, refl! t#0]).to),
  .octor "AltList" ⟨1, #(★ -:> ★), 0, #(), 1, #(t#0 ~[★ -:> ★]~ gt#"List"), gt#"Alternative" • t#0 ⟩,

  /-
  open type Alternative : (* -> *) -> *
  open altMonoid1 : ∀ f. Alternative f -> ∀ u. Monoid (f u)
  open altmonoid2 : ∀ f u. Alternative f -> Monoid (f u)
  -/
  -- .openm "altMonoid2" ⟨2, #(★ -:> ★, ★), 0, #(), 1, #(gt#"Alternative" • t#1),  gt#"Monoid" • (t#1 • t#0)⟩,
  .openm "altMonoid1" ⟨1, #(★ -:> ★), 0, #(), 1, #(gt#"Alternative" • t#0),  ∀[★] gt#"Monoid" • (t#1 • t#0)⟩,
  .odata "Alternative" ((★ -:> ★) -:> ★),


  /-
    inst type MonList : ∀ t u. t ~ List u -> Monoid t
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


#eval! do
  match lookup "altMonoid2" AMCtx with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
      if "altMonoid2" == y then
        let Δ := (Ks1.list ++ Ks2.list).reverse
        let (ζ, Γ) <- pattern_binders (.data .opn) AMCtx Δ n Ts #(⟨"AltList", 2, #(t#0, gt#"Bool"), 1, 1⟩)

        let t3 := inst! "OrdEither" #(t#2) #(t#1, t#0) #(#2, #1, #0).to
        let t4 := inst! "EqOfOrd" #(t#2) #() #(t3).to
        let R' := t4.infer_type AMCtx (ζ ++ Δ) Γ
        return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
      else none
  | _ => none


#guard AMCtx.wf_globals == .some ()
#guard AMCtx.check_open_exhaustive == some ()


end Core.Examples.AlternativeMonoid
