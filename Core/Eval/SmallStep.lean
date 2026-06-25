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
| .cons (.spctor (m1 := m1) (m2 := m2) (n := n) (.data v') c t1 t2 t3) xs => do
  let zs <- Term.is_data v xs
  let z : Constructor := ⟨c, m1, t1, m2, t2, n, t3.to⟩
  if v == v'
  then some (z :: zs)
  else none
| .cons _ _ => none

def get_match (ctors : Vec Constructor m) (ps : Vec (Pattern m) n) : Option (Fin n) :=
  ps.findIdx! (pattern_match ctors)

namespace Test.Eval

def TrueCtor : Vec Constructor 1 := #(⟨"True", 0, #(),0, #(), 0, #()⟩)
def FalseCtor : Vec Constructor 1 := #(⟨"False", 0, #(),0, #(), 0, #()⟩)

def TruePattern : Pattern 1 := #(⟨"True", 0, #(), 0, 0⟩)
def FalsePattern : Pattern 1 := #(⟨"False", 0, #(), 0, 0⟩)
def ps : Vec (Pattern 1) 2 := #(TruePattern, FalsePattern)

#guard get_match TrueCtor ps == some 0
#guard get_match FalseCtor ps == some 1

end Test.Eval

@[simp]
def Term.eval (G : List Global) : Term ->  Option Term

----------------------------------------------------------------
---- Value forms
----------------------------------------------------------------
| .tbind _ _ _ => none
| .lam _ _ => none
| .ctor0 _ => none
| .spctor (.data _) _ _ _ _ => none

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

| .spctor (n := n) .openm x Ts1 Ts2 ss => do
  let m_ss : Vec (Option Term) n := Fun.Vec.to (λ i => eval G (ss i))
  -- let m_ss : Vec.map (eval G) ss.to makes the lean termination checker complain
  match (m_ss).findIdx! Option.isSome with
  | none =>
    let ctors <- Term.is_data .opn ss.to
    let ⟨_, m, p, b⟩ <- get_instance x ctors G
    if h : m == n && pattern_match ctors p
    then
      let τ := Ts2.list.reverse.map su ++ Ts1.list.reverse.map su ++ Subst.id Ty
      let σ' := Constructor.subst_type ctors ++ Subst.id Ty
      let σ := Constructor.subst ctors ++ Subst.id Term
      return b[σ'][τ][σ]
    else none -- stuck
  | some i => do
    let t' <- eval G (ss i)
    if m_ss[i] == t' then
      let ss' := ss.to.set i t'
      return (.spctor .openm x Ts1 Ts2 ss'.to)
    else none


| .mtch m n ss ps bs => do
  let m_ss : Vec (Option Term) m := Fun.Vec.to (λ i => eval G (ss i))
  match (m_ss).findIdx! Option.isSome with
  | none =>
    let ctors <- Term.is_data .cls ss.to
    let τ := Constructor.subst_type ctors ++ Subst.id Ty
    let σ := Constructor.subst ctors ++ Subst.id Term
    let i <- get_match ctors ps.to
    return (bs i)[τ][σ]
  | some i => do
    let t' <- eval G (ss i)
    return (.mtch m n (ss.to.set i t').to ps bs)

-- Λ reduction
| .ctor1 (.appt ty) (.tbind .lamt _ tm) => do
  return (tm[su ty::+0σ])
| .ctor1 (.appt ty) t => do
  let t' <- eval G t
  return (.ctor1 (.appt ty) t')
| .ctor1 (.prj 0) (refl! (.app A _)) => return refl! A
| .ctor1 (.prj 0) (refl! (.arrow A _)) => return refl! A

| .ctor1 (.prj 1) (refl! (.app _ B)) => return refl! B
| .ctor1 (.prj 1) (refl! (.arrow _ B)) => return refl! B

| .ctor1 (.prj n) t => do
  let t' <- eval G t
  return .ctor1 (.prj n) t'


-- λ reduction
| .ctor2 .app (.lam _ t) t2 => do
  return t[su t2::+0σ]
| .ctor2 .app t1 t2 => do
  let t1' <- eval G t1
  return (.ctor2 .app t1' t2)

-- ∀c
| .ctor2 .apptc ((.ctor0 (.refl (Ty.all _ t1)))) (.ctor0 (.refl t2)) => do
  return .ctor0 (.refl t1[su t2::+0σ])
| .ctor2 .apptc t1 t2 => do
   match eval G t1 with
   | none => match eval G t2 with
             | none => none
             | some t2' => return (.ctor2 .apptc t1 t2')
   | some t1' => return (.ctor2 .apptc t1' t2)

-- t ▸ η
| .cast _ (.ctor0 (.refl _)) t => return t
| .cast ty η t2 => do
  let η' <- eval G η
  return .cast ty η' t2



end Core
