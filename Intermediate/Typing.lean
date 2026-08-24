import Intermediate.Global
import Core.Ty
import Surface.Term
import Core.Typing

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
    SpineKinding (.data .cls) y ((.data ⟨x, K, ⟨0, #()⟩⟩)::G) (Core.Ty.is_data x) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data ⟨x, K, ⟨n, ctors⟩⟩)
-- | odata :
--   lookup x G = none ->
--   GlobalWf G (.odata x K)
-- | openm :
--   SpineKinding .openm x G (λ _ => true) T ->
--   lookup x G = none ->
--   GlobalWf G (.openm x T)
| defn {G : GlobalEnv} :
  G&[] ⊢ T : ★ ->
  -- G&[],[] ⊢ t : T ->
  lookup x G = none ->
  GlobalWf G (.defn ⟨x, T, t⟩)
| inst :
  lookup x G = none ->
  lookup cls_name G = some (.odata cls_name K mths) ->
  (e : mths.length = mths_impl.length) ->
  (∀ (i : Nat), (hi : i < mths_impl.length) ->
    ∃ (j : Nat), (hj : j < mths.length) -> mths[j].1 = (mths_impl[i]'hi).1) ->
  -- (Ks1.list ++ Ks2.list).reverse = Δ ->
  -- Core.PatternBinders .opn G Δ n Ts p ζ Γ ->
  GlobalWf G (.instDecl ⟨x, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths_impl⟩)
-- | octor :
--   SpineKinding (.data .opn) x G (Ty.data? .opn G) T ->
--   lookup x G = none ->
--   GlobalWf G (.octor x T)

inductive ListGlobalWf : List Global -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G

def OpenExhaustive (G : Intermediate.GlobalEnv) : Prop :=
  ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q} {cls},
  Intermediate.lookup x G = some (Intermediate.Entry.openm x cls ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  Intermediate.Query G .opn q Ts ->
  ∃ (i : Nat), ∃ n cls_name k1 k2 k3 Ks1 Ks2 tys fds scs mths, G[i]? = some (.instDecl ⟨n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩)
    ∧ ((∃ (j : Nat), ∃ b p, fds[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p)
       ∨ (∃ (j : Nat), ∃ b p, scs[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p)
       ∨ (∃ (j : Nat), ∃ b p, mths[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p))

notation:175 "Ω " G:175 => OpenExhaustive G

end Intermediate
