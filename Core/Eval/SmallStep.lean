import LeanSubst

import Core.Vec
import Core.Ty
import Core.Term
import Core.Global
import Core.Reduction.Definition

import Core.Util
open LeanSubst
open Lilac

namespace Core

@[simp]
def Term.is_data (v : DataConst) : Vec Term m -> Option (Vec Constructor m)
| .nil => return .nil
| .cons (.spctor (m := m) (n := n) (.data v') c t1 t2) xs => do
  let zs <- Term.is_data v xs
  let z : Constructor := ⟨c, m, t1, n, t2.to⟩
  if v == v'
  then some (z :: zs)
  else none
| .cons _ _ => none

def get_match (ctors : Vec Constructor m) (ps : Vec (Pattern m) n) : Option (Pattern m × Fin n) := ps.find (Pattern.match ctors)

@[simp]
def eval (G : List Global) : Term ->  Option Term

----------------------------------------------------------------
---- Value forms
----------------------------------------------------------------
| .tbind _ _ _ => none
| .lam _ _ => none
| .ctor0 _ => none
| .spctor (.data _) _ _ _ => none

----------------------------------------------------------------
---- Normal forms
----------------------------------------------------------------
| .var _ => none

----------------------------------------------------------------
---- Eval Steps
----------------------------------------------------------------
| .defn x => do
  let (_, t) <- lookup_defn G x
  return t

| .spctor (n := n) .openm x Ts ss => do
  let m_ss : Lilac.Fun.Vec (Option Term) n := λ i => eval G (ss i)
  match (m_ss.to).find Option.isSome with
  | none =>
    let ctors <- Term.is_data .opn ss.to
    let ⟨m, p, b⟩ <- get_instance x ctors G
    let τ := Sequ.append_vec (Vec.map su Ts) +0
    let σ := Constructor.subst ctors
    return b[τ:Ty][σ]
  | some (t', i) => do
    let t' <- t'
    return (.spctor .openm x Ts (ss.update t' i))


| .mtch m n ss ps bs => do
  let m_ss : Lilac.Fun.Vec (Option Term) m := λ i => eval G (ss i)
  match (m_ss.to).find Option.isSome with
  | none =>
    let ctors <- Term.is_data .cls ss.to
    let σ := Constructor.subst ctors
    let ⟨_, i⟩ <- get_match ctors ps.to
    return (bs i)[σ]
  | some (t', i) => do
    let t' <- t'
    return (.mtch m n (ss.update t' i) ps bs)

-- Λ reduction
| .ctor1 (.appt ty) (.tbind .lamt _ tm) => do
  return (tm[su ty::+0:Ty])
| .ctor1 (.appt ty) t => do
  let t' <- eval G t
  return (.ctor1 (.appt ty) t')
| .ctor1 v t => none

-- λ reduction
| .ctor2 .app (.lam _ t) t2 => do
  return t[su t2::+0:Term]
| .ctor2 .app t1 t2 => do
  let t1' <- eval G t1
  return (.ctor2 .app t1' t2)

-- ∀c
| .ctor2 .apptc (.tbind .allc _ (.ctor0 (.refl (Ty.all _ t1)))) (.ctor0 (.refl t2)) => do
  return .ctor0 (.refl t1[su t2::+0:Ty])
| .ctor2 .apptc t1 t2 => do
   match eval G t1 with
   | none => match eval G t2 with
             | none => none
             | some t2' => return (.ctor2 .apptc t1 t2')
   | some t1' => return (.ctor2 .apptc t1' t2)

-- t ▸ η
| .cast _ (.ctor0 (.refl _)) t => return t
| .cast ty t1 t2 => do
  let t1' <- eval G t1
  return .cast ty t1' t2



end Core
