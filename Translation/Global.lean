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
