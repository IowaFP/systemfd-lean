import Surface.Global
import Core.Global
import Intermediate.Global

import Surface.Typing
import Intermediate.Typing

import Translation.Ty
import Translation.Term

import Lilac

open Lilac
open LeanSubst

namespace Intermediate

inductive SpCtorVariant : Type where
| openm
| data (c : DataConst)

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

namespace Translation

-- Kind check the types, leaves the terms untouched
def translate_SI : Surface.GlobalEnv -> Option Intermediate.GlobalEnv
| .nil => return .nil
| .cons (.data (n := n) s K ctors) Γ => do
  let Γ' <- translate_SI Γ
  -- let ctors' : Lilac.Vec (String × Core.SpineTy) n :=
  --     ctors.map (λ (s, ⟨n1, v1, n2, v2, n3, v3, R⟩) => (s, ⟨n1, v1.map (·.translate) , n2, v2.map (·.translate), n3, v3.map (·.translate), ⟦R⟧⟩))
  return .cons (.data n s K ctors) Γ'
| .cons (.defn s T t) Γ => do
  let Γ' <- translate_SI Γ
  return .cons (.defn s T t) Γ'
| .cons (.classDecl s Ks scs fds mτs) Γ => none
    -- sorry
| .cons (.instDecl iname spTy ts) Γ => none -- sorry



def Intermediate.OpenExhaustive (G : Intermediate.GlobalEnv) : Prop :=
  ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q},
  Intermediate.lookup x G = some (Intermediate.Entry.openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  Intermediate.Query G .opn q Ts ->
  ∃ (i : Nat), ∃ b p, G[i]? = some (.inst x p b) ∧ Core.Query.Match q p

def translate_IC : Intermediate.GlobalEnv -> Option Core.GlobalEnv
| .nil => return .nil
| .cons (.data n s K ctors) Γ => do
  let Γ' <- translate_IC Γ
  return (.data n s K ctors) :: Γ'
| .cons (.defn n T t) Γ => do
  let Γ' <- translate_IC Γ
  let t' : Core.Term <- Surface.Term.type_directed_translate Γ' [] [] T t
  return (.defn n T t') :: Γ'
| .cons (.odata s K) Γ => do
  let Γ' <- translate_IC Γ
  return .cons (.odata s K) Γ'
| .cons (.openm s spTy) Γ => do
  let Γ' <- translate_IC Γ
  return .cons (.openm s spTy) Γ'
| .cons (.octor s spTy) Γ => do
  let Γ' <- translate_IC Γ
  return .cons (.octor s spTy) Γ'
| .cons (.inst (m := m) s p t) Γ => do
  let Γ' <- translate_IC Γ
  match Core.lookup s Γ' with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) => do
    let Δ := (Ks1.list ++ Ks2.list).reverse
    if s == y && m == n
    then let ⟨ζ, Γ⟩ <- Core.pattern_binders (.data .opn) Γ' Δ n Ts p
         let t' <- t.type_directed_translate Γ' (Δ ++ ζ) Γ R[Subst.add Core.Ty ζ.length]
         return .cons (.inst s p t') Γ'
    else none
  | _ => none


end Translation
