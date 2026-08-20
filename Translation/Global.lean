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

def mk_cls_kind : Vec Core.Kind kc -> Core.Kind
| .nil => ★
| .cons K Ks => K -:> mk_cls_kind Ks

def mk_superclass_om (cls : String) (cls_params : Vec Core.Kind kc) (sc : String) (sc_params : List (Fin kc)) : Core.SpineTy :=
  let cls_ty := (gt#cls).mkApps_nats (List.range cls_params.length)
  let sc_ty := (gt#sc).mkApps_nats sc_params
  ⟨kc, cls_params, 0, #(), 1, #(cls_ty), sc_ty⟩

def mk_method_om (cls : String) (cls_params : Vec Core.Kind kc) (R : Core.SpineTy) : Core.SpineTy :=
  let ⟨na, Ks1, nb, Ks2, nc, cts, R⟩ := R
  let ski := (List.range cls_params.length).map (· + na + nb)
  ⟨kc + na, Ks1 ++ cls_params, nb, Ks2, nc + 1, .cons ((gt#cls).mkApps_nats ski.reverse) cts, R⟩

def mk_fds_om (cls : String) (cls_params : Vec Core.Kind n) (determiners : Vec (Fin n) (kc + 1)) (determinant : Fin n)
  : Core.SpineTy :=
  let ski := (List.range n).map (· + 1)
  ⟨1 + n, cls_params ++ #(cls_params[determinant]), 0, #(), 2, #((gt#cls).mkApps_nats ski.reverse, (gt#cls).mkApps_nats (ski.reverse.replace (determinant + 1) 0)), t#(determinant + 1) ~[cls_params[determinant]]~ t#0⟩


#guard mk_fds_om "Eq" #(★, ★) #(1) 0 == ⟨3, #(★,★,★), 0, #(), 2, #((gt#"Eq" • t#2) • t#1, (gt#"Eq" • t#2) • t#0), t#1 ~[★]~ t#0⟩
-- open fdFwd :: ∀ t u u'. Equal t u -> Equal t u' -> u ~ u'
-- open fdFWd :: ∀[★]∀[★]∀[★] Equal 2 1 -> Equal 2 0 -> 1 ~ 0


#eval mk_fds_om "Eq" #(★, ★) #(0) 1 == ⟨3, #(★,★,★), 0, #(), 2, #((gt#"Eq" • t#2) • t#1, (gt#"Eq" • t#0) • t#1), t#2 ~[★]~ t#0⟩
-- open fdBwk :: ∀ t u t'. Equal t u -> Equal t' u -> t ~ t'
-- open fdBWk :: ∀[★]∀[★]∀[★]. Equal 2 1 -> Equal 0 1 -> 2 ~ 0

def mk_inst_mths (Γ' : Intermediate.GlobalEnv) (C iname : String) : List (String × Surface.Term) -> Option Intermediate.GlobalEnv
| List.nil => some .nil
| .cons (mn, tm) ts => do
  let ts' <- mk_inst_mths Γ' C iname ts
  match Intermediate.lookup mn Γ' with
  | some (.openm mn' cls spTy) =>
    if mn == mn' && C == cls
    then return ((.inst (m := 1) mn C #(⟨iname, 1, #(t#0), 0, 1⟩) tm) :: ts') -- TODO: Fix Pattern
    else none
  | _ => none

-- Kind check the types, leaves the terms untouched
def translate_SI : Surface.GlobalEnv -> Option Intermediate.GlobalEnv
| .nil => return .nil
| .cons (.data (n := n) s K ctors) Γ => do
  let Γ' <- translate_SI Γ
  -- TODO : Kind check each of the constructor types
  if (Intermediate.lookup s Γ').isNone
  then return .cons (.data n s K ctors) Γ'
  else none
| .cons (.defn s T t) Γ => do
  let Γ' <- translate_SI Γ
  -- TODO: Kind check T
  if (Intermediate.lookup s Γ').isNone
  then return .cons (.defn s T t) Γ'
  else none
| .cons (.classDecl s Ks scs fds mτs) Γ => do
  let Γ' <- translate_SI Γ
  if (Intermediate.lookup s Γ').isNone
  then
    let od : Intermediate.Global := .odata s (mk_cls_kind Ks)
    let scs : Intermediate.GlobalEnv := scs.map (λ (n, sc, params) => .openm n s (mk_superclass_om s Ks sc params))
    let mτs : Intermediate.GlobalEnv := mτs.map (λ (n, spTy) => .openm n s (mk_method_om s Ks spTy))
    -- TODO: names s and scs fds mτs are distinct
    -- TODO: FunDep structure validation
    let fds : Intermediate.GlobalEnv := fds.map (λ ⟨n, _, dems, det⟩ => .openm n s (mk_fds_om s Ks dems det))
    fds ++ scs ++ mτs ++ (od :: Γ')
  else none

| .cons (.instDecl iname spTy@⟨na, Ks1, nb, Ks2, nc, As, R⟩ ts) Γ => do
  let Γ' <- translate_SI Γ
  match Intermediate.lookup iname Γ' with
  | some _ => none
  | none =>
    match R.spine with
    | none => none
    | some (C, Tys) =>
      match Intermediate.lookup C Γ' with
      | some (.odata cls _) => do
        if C == cls then
        let ts' : Intermediate.GlobalEnv <- mk_inst_mths Γ' C iname ts
        return ts' ++
          (.octor iname spTy) :: Γ'
        else none
      | _ => none


notation: 175 "⟦" G "⟧" => translate_SI G

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
| .cons (.openm s _ spTy) Γ => do
  let Γ' <- translate_IC Γ
  return .cons (.openm s spTy) Γ'
| .cons (.octor s spTy) Γ => do
  let Γ' <- translate_IC Γ
  return .cons (.octor s spTy) Γ'
| .cons (.inst (m := m) s _ p t) Γ => do
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

notation: 175 "⟦" G "⟧" => translate_IC G


end Translation
