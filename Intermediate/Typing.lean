import Intermediate.Global
import Core.Ty
import Surface.Term

import Lilac
open Lilac

namespace Intermediate


def Query (G : GlobalEnv) (c : DataConst) (qs : Vec String m) (Ts : Vec Core.Ty m) : Prop :=
  VecTyping (lookup_ctor? G c · ·) qs Ts


inductive Kinding (G : List Intermediate.Global) : List Core.Kind -> Core.Ty -> Core.Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t#x K
| global :
  lookup_kind G x = some K ->
  Kinding G Δ gt#x K
| arrow :
  Kinding G Δ A ★ ->
  Kinding G Δ B ★ ->
  Kinding G Δ (A -:> B) ★
| all :
  Kinding G (K::Δ) P ★ ->
  Kinding G Δ (∀[K] P) ★
| app :
  Kinding G Δ f (A -:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f • a) B
| eq :
  Kinding G Δ A K ->
  Kinding G Δ B K ->
  Kinding G Δ (A ~[K]~ B) ★

notation:170 G:170 "&" Δ:170 " ⊢ " A:170 " : " K:170 => Kinding G Δ A K

def Ty.data? (c : DataConst) (G : List Global) (A : Core.Ty) : Bool :=
  match A.spine with
  | some (x, _) => is_data c G x
  | none => false

end Intermediate
