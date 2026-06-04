import LeanSubst
import Core.Ty
import Core.Infer.Kind
import Core.Global
import Core.Vec
import Lilac

open LeanSubst
open Lilac

namespace Core

namespace Infer.Ty.Test

def bool_ctors_sig : SpineTy := ⟨0, Vec.nil, 0, Vec.nil, gt#"Bool"⟩

def G : List Global := [
  .odata "Eq" (★ -:> ★)
  , .data 2 "Bool" ★ #𝓋[ ("True",  bool_ctors_sig) , ("False", bool_ctors_sig) ]
  -- , .data 0 "Empty" ★ Vec.nil
  ]


def R : Ty := gt#"Eq" • t#0
def A : Ty := (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)

#guard R.spine == .some ("Eq", [t#0])

end Infer.Ty.Test

@[simp]
def Ty.valid_data (c : DataConst) (G : List Global) : Ty -> Option Unit
| A => do
  let (x, _) <- A.spine
  if is_data c G x
  then return () else none

def Ty.valid_spine_kinding (G : List Global) : SpineTy -> Option Unit
  | ⟨_, Ks, n, Ts, R ⟩ => do
  let Δ := Vec.to_list Ks
  let mks : Vec (Option Kind) n <- Ts.map (λ t => t.infer_kind G Δ)
  let ks <- mks.seq
  if ks.elems_eq_to ★
  then let k <- R.infer_kind G Δ
       if k == ★ then some ()
       else none
  else none

def Ty.kind_preamble (G : List Global) (Δ : List Kind) : List Ty -> Ty -> Option Ty
| [], τ  => return τ
| .cons a as, ∀[K] τ => do
  let K' <- a.infer_kind G Δ
  if K == K' then
    (τ[su a :: +0]).kind_preamble G Δ as
  else none
| _ , _ => none

def query (G : GlobalEnv) (c : DataConst) : (ps : Vec String m) -> (qs : Vec Ty m) -> Option Unit
| .nil, .nil => some ()
| .cons x xs, .cons y ys => do
  let _ <- query G c xs ys
  if lookup_ctor? G c x y
  then some ()


def query_match : Vec String m -> Pattern m -> Option Unit
| .nil, _ => some ()
| .cons x xs, .cons y ys => do
  let _ <- query_match xs ys
  if x == y.1 then some () else none


@[simp]
def pattern_binders (G : List Global) (Δ : List Kind) : (m : Nat) -> Vec Ty m -> Pattern n -> Option (List Ty)
| 0, _, _ => some []
| m + 1, .cons R' Ss, .cons ⟨c, na, As, nb⟩ ps => do
  let ℓ <- pattern_binders G Δ m Ss ps
  let ⟨na', Ks, nb', Ts, R⟩ <- lookup_spine_type G c
  if nb == nb' && na' == na
  then
    let τ := Sequ.append_vec (As.map su) +0
    let mAsk := As.map (λ t => t.infer_kind G Δ)
    let Ask <- mAsk.seq
    if Ask.eq Ks
    then
      let Ts' := Ts.map (λ T => T[τ])
      if R[τ] == R' then return (Ts'.to_list ++ ℓ) else none
    else none
  else none
| _, _ , _ => none

-- Builds a matrix of all possible combination of constructor tags given a vector of types
def build_sat_matrix {m : Nat} (G : GlobalEnv) (Ss : Vec Ty m) : Option ((n : Nat) × Fun.Vec (Vec String m) n) := do

  sorry

-- returns a matrix of constructor tags from a pattern matrix
def pattern_to_tags (ps : Fun.Vec (Pattern m) n) : Fun.Vec (Vec String m) n := λ i =>
 Fun.Vec.to (λ j => ((ps i).get_elem j).1)

-- Checks that the patterns are exhaustive
def check_exhaustive (G : GlobalEnv) : Vec Ty m -> Fun.Vec (Pattern m) n -> Option Unit
| _ , _ => do return ()


@[simp]
def Term.infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x => do
  let T <- Γ[x]?
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T
| .defn x => do
  let ⟨T, _⟩ <- lookup_defn G x
  let Tk <- T.infer_kind G Δ
  if Tk == .base
    then return T
    else none
| spctor (n := n) (m := m) (.data d) x As ts => do
  let ⟨m', Ks, n', Ts, R⟩ <- lookup_spine_type G x
  let mKs := (As.map (λ y => Ty.infer_kind G Δ y))
  let Ks' <- mKs.seq
  if Ks.eq Ks' && m' == m
  then
    let mτs := Fun.Vec.to (λ i => Term.infer_type G Δ Γ (ts i))
    let τs <- mτs.seq
    let τ := Sequ.append_vec (Vec.map su As) +0
    let Ts := Ts.map (λ x => x[τ])
    if lookup_ctor? G d x R && Ts.eq τs && n' == n
    then return R[τ]
    else none
  none
| spctor (n := n) (m := m) .openm x As ts => do
  let ⟨m', Ks, n', Ts, R⟩ <- lookup_spine_type G x
  let mKs := As.map (λ y => Ty.infer_kind G Δ y)
  let Ks' <- mKs.seq
  if Ks.eq Ks' && m' == m
  then
    let τ := Sequ.append_vec (Vec.map su As) +0
    let mτs := Fun.Vec.to (λ i => Term.infer_type G Δ Γ (ts i))
    let τs : Vec Ty n <- mτs.seq
    let Ts := Ts.map (λ x => x[τ:Ty])
    let vs := Vec.map (Ty.valid_data .opn G) τs
    let _ <- vs.seq
    if Ts.eq τs && n' == n
    then return R[τ]
    else none
  none
| .mtch m n ss ps ts => do
  -- infer the type of scrutinees
  let smτs : Lilac.Fun.Vec (Option Ty) m := λ i => (infer_type G Δ Γ (ss i))
  let Ss <- smτs.to.seq

  let mTs : Vec (Option Unit) m := Ss.map (Ty.valid_data .cls G)
  let _ <- mTs.seq

  let mξs : Lilac.Fun.Vec (Option (List Ty)) n := λ i => pattern_binders (m := m) G Δ Ss (ps i)
  let ξs <- mξs.to.seq
  let mTs' : Lilac.Fun.Vec (Option Ty) n := λ i => (ts i).infer_type G Δ ((ξs.get_elem i) ++ Γ)
  -- TODO: Query business to make sure matches are exhaustive
  -- Plan:
  -- Get the types of all the scrutinees
  -- get the possible tags/constructor names for each of the scrutinee datatype
  -- given a permutation of tags, the function spits out the row in the pattern vector
  let _ <- check_exhaustive G Ss ps
  let Ts' <- mTs'.to.seq
  let T <- Ts'.get_elem_if_eq
  return T

| .cast R c t => do
  let e <- c.infer_type G Δ Γ
  let (K, A, B) <- e.is_eq_some
  let RK <- R.infer_kind G (K :: Δ)
  let _ <- RK.base_kind
  let tA <- t.infer_type G Δ Γ
  if R[su A::+0] == tA then return R[su B::+0] else none
| .lam A t => do
  let Ak <- A.infer_kind G Δ
  let _ <- Ak.base_kind
  let R <- t.infer_type G Δ (A::Γ)
  let Rk <- R.infer_kind G Δ
  let _ <- Rk.base_kind
  return A -:> R

| .ctor0 (.refl A) => do
  let Ak <- A.infer_kind G Δ
  return (A ~[Ak]~ A)

| .ctor1 (.appt τ) t => do
  let τk <- τ.infer_kind G Δ
  let T <- t.infer_type G Δ Γ
  let (K, T) <- T.is_all_some
  if τk == K
  then return T[.su τ::+0]
  else none
| .ctor1 (.prj 0) t => do
   let T <- t.infer_type G Δ Γ
   let (K2, AC, BD) <- T.is_eq_some
   -- TODO is_app_some or is_arrow_some
   let (A, C) <- AC.is_app_some
   let (B, D) <- BD.is_app_some
   let Ak <- A.infer_kind G Δ
   let Bk <- B.infer_kind G Δ
   let Ck <- C.infer_kind G Δ
   let Dk <- D.infer_kind G Δ
   let (KA1, KA2) <- Ak.is_arrow
   let (KB1, KB2) <- Bk.is_arrow
   if Ck == Dk && KA1 == KB1 && Ck == KA1 && KA2 == KB2 && KA2 == K2
   then return (A ~[KA1 -:> KA2]~ B)
   else none
| .ctor1 (.prj 1) t => do
   let T <- t.infer_type G Δ Γ
   let (K2, AC, BD) <- T.is_eq_some
   -- TODO is_app_some or is_arrow_some
   let (A, C) <- AC.is_app_some
   let (B, D) <- BD.is_app_some
   let Ak <- A.infer_kind G Δ
   let Bk <- B.infer_kind G Δ
   let Ck <- C.infer_kind G Δ
   let Dk <- D.infer_kind G Δ
   let (KA1, KA2) <- Ak.is_arrow
   let (KB1, KB2) <- Bk.is_arrow
   if Ck == Dk && KA1 == KB1 && Ck == KA1 && KA2 == KB2 && KA2 == K2
   then return (C ~[KA1]~ D)
   else none

| .ctor2 .apptc f a => do
  let T1 <- f.infer_type G Δ Γ
  let _ <- T1.infer_kind G Δ
  let (Kf, A, B) <- T1.is_eq_some
  let _ <- Kf.base_kind
  let (AK, AT) <- A.is_all_some
  let (BK, BT) <- B.is_all_some
  let T2 <- a.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (Ka, C, D) <- T2.is_eq_some
  if AK == BK && Ka == AK
  then return ((AT[su C::+0:Ty]) ~[★]~ (BT[su D ::+0 :Ty])) else none

| .ctor2 .app f a => do
  let F <- f.infer_type G Δ Γ
  let (A, B) <- F.is_arrow_some
  let A' <- a.infer_type G Δ Γ
  let Ak' <- A'.infer_kind G Δ
  let _ <- Ak'.base_kind
  if A == A' then return B else none

| .tbind .lamt K t => do
  let T <- t.infer_type G (K::Δ) (Γ[+1:Ty])
  let Tk <- (∀[K]T).infer_kind G Δ
  let bk <- Tk.base_kind
  if bk == () then return (∀[K] T) else none
| .tbind .allc K t => do
  let T1 <- infer_type G (K::Δ) (Γ[+1:Ty]) t
  let (Tk, A, B) <- T1.is_eq_some
  let _ <- Tk.base_kind
  return ((∀[K]A) ~[Tk]~ (∀[K]B))

| _ => none


def spine_kinding (G : List Global) :  SpineTy -> Option Unit
| ⟨_, Ks, _, Ts, R⟩ => do
  let Δ := Ks.to_list
  let mTKs := Ts.map (λ T => T.infer_kind G Δ)
  let TKs <- mTKs.seq
  let RK <- R.infer_kind G Δ
  if TKs.elems_eq_to ★ && RK == ★
  then some () else none

namespace Core
