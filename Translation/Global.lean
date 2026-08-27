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

@[simp] abbrev TM α := Except Std.Format α


namespace Option
def toTM (e : Std.Format) : Option α -> Except Std.Format α
| none => Except.error e
| some e => Except.pure e
end Option

instance : MonadLift TM IO where
  monadLift tm := match tm with
  | .ok a => return a
  | .error s => .throw (.userError s.pretty)

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

def mk_inst_mth_SI (Γ' : Intermediate.GlobalEnv) (C iname : String)
  (mτs : List (String × Core.SpineTy)) (mn : String) (tm : Surface.Term) :
  TM (String × (m : Nat) × Core.Pattern m × Surface.Term) :=
  match List.lookup mn mτs with
  | .some ⟨na, Ks1, nb, Ks2, nc, As, R⟩ =>
    match Intermediate.lookup iname Γ' with
    | some (.octor iname' _) =>
      if nc == 1 && iname == iname' then
      return ⟨mn, 1, #(⟨iname, 1, #(t#0), 0, 1⟩), tm⟩ -- TODO: Fix Pattern
      else .error "mk_inst_mth_SI"
    | _ => .error "mk_inst_mth_SI iname lookup"
  | _ => .error "mk_inst_mth_SI"


def mk_inst_mths_SI (Γ' : Intermediate.GlobalEnv) (C iname : String) (mτs : List (String × Core.SpineTy))
 : List (String × Surface.Term) ->
 TM (List (String × (n : Nat) × Core.Pattern n × Surface.Term))
| List.nil => return List.nil
| .cons (mn, tm) ts => do
  let ts' <- mk_inst_mths_SI Γ' C iname mτs ts
  let t <- mk_inst_mth_SI Γ' C iname mτs mn tm
  return (t :: ts')


-- Kind check the types, leaves the terms untouched
def translate_SI : Surface.GlobalEnv -> TM Intermediate.GlobalEnv
| .nil => return .nil
| .cons (.data (n := n) s K ctors) Γ => do
  let Γ' <- translate_SI Γ
  -- TODO : Kind check each of the constructor types
  if (Intermediate.lookup s Γ').isNone && ctors.all (λ (c, _) => (Intermediate.lookup c Γ').isNone)
  then return .cons (.data ⟨s, K, ⟨n, ctors⟩⟩) Γ'
  else .error "translate_SI data"
| .cons (.defn s T t) Γ => do
  let Γ' <- translate_SI Γ
  -- TODO: Kind check T
  if (Intermediate.lookup s Γ').isNone
  then return .cons (.defn ⟨s, T, t⟩) Γ'
  else .error "translate_SI defn"
| .cons (.classDecl s Ks /-scs fds-/ mτs) Γ => do
  let Γ' <- translate_SI Γ
  if (Intermediate.lookup s Γ').isNone
  then
    -- let od : Intermediate.Global := .odata s (mk_cls_kind Ks)
    let scs := [] -- scs.map (λ (n, sc, params) =>  ⟨n, (mk_superclass_om s Ks sc params)⟩)
    let fds := [] -- fds.map (λ ⟨n, _, dems, det⟩ => ⟨n, (mk_fds_om s Ks dems det)⟩)
    let mτs := mτs.map (λ (n, spTy) =>  ⟨n, (mk_method_om s Ks spTy)⟩)
    -- TODO: names s and scs fds mτs are distinct
    -- TODO: FunDep structure validation
    return (.classDecl ⟨s, (mk_cls_kind Ks), fds, scs, mτs⟩ :: Γ')
  else .error "translate_SI classDecl"

| .cons (.instDecl iname ⟨na, Ks1, nb, Ks2, nc, As, R⟩ ts) Γ => do
  let Γ' <- translate_SI Γ
  match Intermediate.lookup iname Γ' with
  | none =>
    let (cls_name, _) <- Option.toTM "translate_SI R.spine" (R.spine)
    match Intermediate.lookup cls_name Γ' with
    | some (.odata cls_name' K' mτs) =>
        if cls_name' == cls_name && mτs.length == ts.length
        then let mths <- mk_inst_mths_SI Γ' cls_name iname mτs ts
             if mτs.length == mths.length then
                return (.cons (.instDecl ⟨iname, cls_name, na, nb, nc, Ks1, Ks2, As, [], [], mths⟩) Γ')
             else .error "translate_SI instDecl mτs.length"
        else .error "translate_SI instDecl cls_name"
    | _ => .error "translate_SI instDecl odata"
  | _ => .error "translate_SI instDecl lookup cls_name"


notation: 175 "⟦" G "⟧" => translate_SI G

def mk_inst_mth_IC (G : Core.GlobalEnv) (mn : String) (m : Nat) (p : Core.Pattern m) (t : Surface.Term) :
  TM Core.Global := do
  match Core.lookup mn G with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) => do
    let Δ := (Ks1.list ++ Ks2.list).reverse
    if mn == y && m == n
    then let ⟨ζ, Γ⟩ <- Option.toTM "Pattern Binders" (Core.pattern_binders (.data .opn) G Δ n Ts p)
         let t' <- Option.toTM
           ("G :" ++ G.repr max_prec ++  Std.Format.line ++ "Δ : " ++ (Δ ++ ζ).repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "t : " ++  t.repr max_prec ++ Std.Format.line
            ++ "R : " ++  (R[Subst.add Core.Ty ζ.length]).repr max_prec ++ Std.Format.line)
           (t.type_directed_translate G (Δ ++ ζ) Γ R[Subst.add Core.Ty ζ.length])
         return .inst mn p t'
    else Except.error "pat sizes don't match"
  | _ => Except.error "lookup failed"

def mk_inst_mths_IC (G : Core.GlobalEnv) :
  List (String × (m : Nat) × Core.Pattern m × Surface.Term) ->
  TM Core.GlobalEnv
| .nil => return .nil
| .cons ⟨mn, m, p, t⟩ ms => do
  let ms' <- mk_inst_mths_IC G ms
  let i' <- mk_inst_mth_IC G mn m p t
  return (i' :: ms')

def translate_IC : Intermediate.GlobalEnv -> TM Core.GlobalEnv
| .nil => return .nil
| .cons (.data ⟨s, K, ⟨n, ctors⟩⟩) Γ => do
  let Γ' <- translate_IC Γ
  return (.data n s K ctors) :: Γ'
| .cons (.defn ⟨s, T, t⟩) Γ => do
  let Γ' <- translate_IC Γ
  let t' : Core.Term <- Option.toTM "defn translate" (t.type_directed_translate Γ' [] [] T)
  return (.defn s T t') :: Γ'
| .cons (.classDecl ⟨s, K, fds, scs, mths⟩) Γ => do
  let Γ' <- translate_IC Γ
  return mths.map (λ (n, spTy) => .openm n spTy)
         -- ++ scs.map (λ (n, spTy) => .openm n spTy)
         -- ++ fds.map (λ (n, spTy) => .openm n spTy)
         ++ [.odata s K] ++ Γ'

| .cons (.instDecl ⟨iname, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩) Γ => do
  let Γ' <- translate_IC Γ
  -- let fds' : Core.GlobalEnv <- fds.mapM (λ ⟨n, m, p, t⟩ => none)
  let octor := [.octor iname ⟨k1, Ks1, k2, Ks2, k3, (tys.zip (Vec.range tys.length)).map (λ (T, n) => t#n ~[★]~ T),
                       (gt#cls_name).mkApps_nats (List.range tys.length).reverse⟩ ]
  let mths' <- (mk_inst_mths_IC (octor ++ Γ') mths)
  return (mths' ++ octor ++ Γ')



notation: 175 "⟦" G "⟧" => translate_IC G


end Translation
