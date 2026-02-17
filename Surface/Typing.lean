import LeanSubst
import Core.Vec

import Surface.Ty
import Surface.Global


inductive Surface.Kinding (G : List Surface.Global) : List Surface.Kind -> Surface.Ty -> Surface.Kind -> Prop
| var :
  Δ[x]? = some K ->
  Surface.Kinding G Δ t`#x K
| global :
  Surface.lookup_kind G x = some K ->
  Kinding G Δ gt`#x K
| arrow :
  Surface.Kinding G Δ A (.base b1) ->
  Surface.Kinding G Δ B (.base b2) ->
  Surface.Kinding G Δ (A `-:> B) `★
| all :
  Surface.Kinding G (K::Δ) P `★ ->
  Surface.Kinding G Δ (`∀[K] P) `★
| app :
  Surface.Kinding G Δ f (A `-:> B) ->
  Surface.Kinding G Δ a A ->
  Surface.Kinding G Δ (f `• a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Surface.Kinding G Δ A K
