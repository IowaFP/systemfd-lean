import LeanSubst
import Core.Vec

import Surface.Ty
import Surface.Term
import Surface.Global


namespace Surface

@[simp]
abbrev KindEnv := List Kind

@[simp]
abbrev TyEnv := List Ty


inductive Kinding (G : GlobalEnv) : KindEnv -> Ty -> Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t`#x K
| global :
  lookup_kind G x = some K ->
  Kinding G Δ gt`#x K
| arrow :
  Kinding G Δ A `★ ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A `-:> B) `★
| «then» :
  Kinding G Δ A `◯ ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A `=:> B) `★
| all :
  Kinding G (K::Δ) P `★ ->
  Kinding G Δ (`∀[K] P) `★
| app :
  Kinding G Δ f (A `-:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f `• a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Kinding G Δ A K

inductive ValidCtor (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidCtor x T
| all :
  ValidCtor x P ->
  ValidCtor x (`∀[K] P)
| arrow :
  ValidCtor x B ->
  ValidCtor x (A `-:> B)

-- Valid Class Methods are of the form
-- ∀αs (x βs) => B
inductive ValidClassMethodTy (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidClassMethodTy x T
| all :
  ValidClassMethodTy x P ->
  ValidClassMethodTy x (`∀[K] P)
| arrow :
  A.spine = some (x, sp) ->
  ValidClassMethodTy x (A `=:> B)

inductive ValidOpenKind : Kind -> Prop where
| base : ValidOpenKind `◯
| arrow : ValidOpenKind B -> ValidOpenKind (A `-:> B)


inductive ValidClassInstTy (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidClassInstTy x T

end Surface
