import Surface.Ty
import Surface.Global
import Surface.Term

import Surface.Examples.Boolean

import Translation.Global

namespace Surface.Examples.MultiparamClasses


def TruePat : String × (n : Nat) × Lilac.Vec Core.Ty n × Nat × Nat := ⟨"True", 0, #(), 0, 0⟩
def FalsePat : String × (n : Nat) × Lilac.Vec Core.Ty n × Nat × Nat :=  ⟨"False", 0, #(), 0, 0⟩


def mbenv : GlobalEnv := [
  .defn "test_plus_poly" (∀[★] (t#0 ~[★]~ gt#"Bool") -:> gt#"Bool" -:> gt#"Bool" -:> t#0)
    (Λˢ[★]λˢ[t#0 ~[★]~ gt#"Bool"] (g`#"plus" `•ᵤ #(t#0, t#0, gt#"Bool") `•ₑ #() `•ₜ .nil)),


  .defn "test_plus" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool") (g`#"plus" `•ᵤ #(gt#"Bool", gt#"Bool", gt#"Bool") `•ₑ #() `•ₜ .nil),


  -- .instDecl ""
  .instDecl "PB" ⟨3, #(★, ★, ★), 0, #(), 3, #(t#2 ~[★]~ gt#"Bool", t#1 ~[★]~ gt#"Bool", t#0 ~[★]~ gt#"Bool"), ((gt#"Plus" • t#2) • t#1) • t#0⟩
    [("plus", λˢ[gt#"Bool"]λˢ[gt#"Bool"]
               mtch' #((`#1, gt#"Bool"), (`#0, gt#"Bool"))
               #( (#(TruePat, TruePat), Boolean.TrueCtor)
                , (#(TruePat, FalsePat), Boolean.TrueCtor)
                , (#(FalsePat, TruePat), Boolean.TrueCtor)
                , (#(FalsePat, FalsePat), Boolean.FalseCtor))

      )],

  .classDecl "Plus" #(★, ★, ★) [] [("plus", ⟨0, #(), 0, #(), 0, #(), (t#2 -:> t#1 -:> t#0)⟩)],


  -- .data (n := 2) "Maybe" (★ -:> ★) #(("Just", ⟨1, #(★), 0, #(), 1, #(t#0), gt#"Maybe" • t#0⟩ ),
  --                                 ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩))
  ] ++ Surface.Examples.Boolean.benv

#eval mbenv
#eval!  Translation.translate_SI mbenv
def Γ := do
  let benv' <- (Translation.translate_SI mbenv)
  Translation.translate_IC benv'

#eval! Γ

#guard (do let Γ <- Γ
           return Γ.wf_globals) == .ok ()




end Surface.Examples.MultiparamClasses
