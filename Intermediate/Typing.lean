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


inductive SpineKinding (sv : SpCtorVariant) (x : String) (G : GlobalEnv) (test : Core.Ty -> Bool) : Core.SpineTy -> Prop where
| valid {Ks1 : Vec Core.Kind m1} {Ks2 : Vec Core.Kind m2} {Ts : Vec _ n} :
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  (∀ (i : Fin n), G&Δ ⊢ Ts[i] : ★) ->
  G&Δ ⊢ R : ★ ->
  test R ->
  (sv = .openm -> ∀ (i : Fin n), Intermediate.Ty.data? .opn G Ts[i]) ->
  SpineKinding sv x G test ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩


inductive GlobalWf : GlobalEnv -> Global -> Prop where
| data {G : GlobalEnv} {ctors : Vec (String × Core.SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    SpineKinding (.data .cls) y ((.data 0 x K #())::G) (Core.Ty.is_data x) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data n x K ctors)
| odata :
  lookup x G = none ->
  GlobalWf G (.odata x K)
| openm :
  SpineKinding .openm x G (λ _ => true) T ->
  lookup x G = none ->
  GlobalWf G (.openm x T)
| defn {G : GlobalEnv} :
  G&[] ⊢ T : ★ ->
  -- G&[],[] ⊢ t : T ->
  lookup x G = none ->
  GlobalWf G (.defn x T t)
| inst :
  lookup x G = some (.openm x ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  -- Core.PatternBinders .opn G Δ n Ts p ζ Γ ->
  GlobalWf G (.inst x p t)
| octor :
  SpineKinding (.data .opn) x G (Ty.data? .opn G) T ->
  lookup x G = none ->
  GlobalWf G (.octor x T)

inductive ListGlobalWf : List Global -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G

end Intermediate
