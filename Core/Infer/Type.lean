import LeanSubst
import Core.Ty
import Core.Infer.Kind
import Core.Infer.Exhaustiveness
import Core.Global
import Core.Vec
import Lilac

open LeanSubst
open Lilac

namespace Core

namespace Infer.Ty.Test

def bool_ctors_sig : SpineTy := ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩

def G : List Global := [
  .odata "Eq" (★ -:> ★)
  , .data 2 "Bool" ★ #( ("True",  bool_ctors_sig) , ("False", bool_ctors_sig) )
  -- , .data 0 "Empty" ★ Vec.nil
  ]


def R : Ty := gt#"Eq" • t#0
def A : Ty := (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)

#guard R.spine == .some ("Eq", [t#0])

end Infer.Ty.Test


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

def query_patterns (q : Vec String m) (ps : Vec (Pattern m) n) : Option (Fin n)
 := Vec.findIdx! (λ p => (query_match q p).isSome) ps

@[simp]
def pattern_binders (G : List Global) (Δ : List Kind) : (m : Nat) -> Vec Ty m -> Pattern n -> Option (List Kind × List Ty)
| 0, _, _ => some ([], [])
| m + 1, .cons R' Ss, .cons ⟨c, na, As, nb, nc⟩ ps => do
  let (ℓ1, ℓ2) <- pattern_binders G Δ m Ss ps
  let ⟨na', Ks1, nb', Ks2, nc', Ts, R⟩ <- lookup_spine_type G c
  if nb == nb' && na' == na && nc == nc'
  then
    let mAsk := As.map (λ t => t.infer_kind G Δ)
    let Ask <- mAsk.sequence
    if Ask.beq Ks1
    then
      let σ := As.list.reverse.map su ++ Subst.id Ty
      let Ts := Ts[σ.lift nb]⟨.add Ty ℓ1.length⟩
      --(ℓ1 ++ Ks2.list.reverse, ℓ2 ++ Ts.list.reverse)
      --some ⟨[], [R[σ.lift nb], R'⟨.add Ty nb⟩]⟩
      if R[σ.lift nb] == R'⟨.add Ty nb⟩ then return (ℓ1 ++ Ks2.list.reverse, ℓ2 ++ Ts.list.reverse) else none
    else none
  else none
| _, _ ,_ => none


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
| spctor (n := n) (m1 := m1) (m2 := m2) (.data d) x As Bs ts => do
  let ⟨m1', Ks1, m2', Ks2, n', Ts, R⟩ <- lookup_spine_type G x
  let mKsA := (As.map (λ y => Ty.infer_kind G Δ y))
  let KsA <- mKsA.sequence
  let mKsB := Bs.map (λ y => Ty.infer_kind G Δ y)
  let KsB <- mKsB.sequence
  if KsA.beq Ks1 && KsB.beq Ks2 && m1 == m1' && m2 == m2'
  then
    let mτs := Fun.Vec.to (λ i => Term.infer_type G Δ Γ (ts i))
    let τs <- mτs.sequence
    let τ := (As.list ++ Bs.list).reverse.map su ++ Subst.id Ty
    let Ts := Ts.map (λ x : Ty => x[τ])
    if lookup_ctor? G d x R && Ts.beq τs && n' == n
    then return R[τ]
    else none
  none
| spctor (n := n) (m1 := m1) (m2 := m2) .openm x As Bs ts => do
  let ⟨m1', Ks1, m2', Ks2, n', Ts, R⟩ <- lookup_spine_type G x
  let mKsA := (As.map (λ y => Ty.infer_kind G Δ y))
  let KsA <- mKsA.sequence
  let mKsB := Bs.map (λ y => Ty.infer_kind G Δ y)
  let KsB <- mKsB.sequence
  if KsA.beq Ks1 && KsB.beq Ks2 && m1 == m1' && m2 == m2'
  then
    let τ := (As.list ++ Bs.list).reverse.map su ++ Subst.id Ty
    let mτs := Fun.Vec.to (λ i => Term.infer_type G Δ Γ (ts i))
    let τs : Vec Ty n <- mτs.sequence
    let Ts' := Ts.map (λ x : Ty => x[τ])
    let vs := Vec.map (Ty.valid_data .opn G) Ts
    let _ <- vs.sequence
    if Ts'.beq τs && n' == n
    then return R[τ]
    else none
  none
| .mtch m n ss ps ts => do
  -- infer the type of scrutinees
  let smτs : Lilac.Fun.Vec (Option Ty) m := λ i => (infer_type G Δ Γ (ss i))
  let Ss <- smτs.to.sequence
  let mTs : Vec (Option Unit) m := Ss.map (Ty.valid_data .cls G)
  let _ <- mTs.sequence
  -- infer the type of binders
  let mξs : Lilac.Fun.Vec (Option (List Kind × List Ty)) n := λ i => pattern_binders (m := m) G Δ Ss (ps i)
  let ζξ <- mξs.to.sequence
  let (ζ , ξ) := ζξ.unzip
  -- infer the type of each branch by updating the typing and kinding ctx
  let mTs' : Lilac.Fun.Vec (Option Ty) n := λ i => (ts i).infer_type G (ζ[i] ++ Δ) (ξ[i] ++ Γ)
  -- check the patterns are exhaustive
  let _ <- check_exhaustive G Ss ps.to
  let Ts' <- mTs'.to.sequence
  let T <- Ts'.get_elem_if_eq -- TODO : Fix me, map (λ T : Ty => T⟨.add Ty ((Vec.max ζ) - ζ[i].length) ⟩)
  if T⟨.sub Ty ζ.length⟩⟨.add Ty ζ.length⟩ == T
    then return T⟨.sub Ty ζ.length⟩ else none

| .cast R c t => do
  let e <- c.infer_type G Δ Γ
  let (K, A, B) <- e.is_eq_some
  let RK <- R.infer_kind G (K :: Δ)
  let _ <- RK.base_kind
  let tA <- t.infer_type G Δ Γ
  if R[su A::+0σ] == tA then return R[su B::+0σ] else none
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
  then return T[.su τ::+0σ]
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
  then return ((AT[su C::+0σ]) ~[★]~ (BT[su D::+0σ])) else none

| .ctor2 .app f a => do
  let F <- f.infer_type G Δ Γ
  let (A, B) <- F.is_arrow_some
  let A' <- a.infer_type G Δ Γ
  let Ak' <- A'.infer_kind G Δ
  let _ <- Ak'.base_kind
  if A == A' then return B else none

| .tbind .lamt K t => do
  let T : Ty <- t.infer_type G (K::Δ) Γ⟨.succ Ty⟩
  let Tk <- (∀[K]T).infer_kind G Δ
  let bk <- Tk.base_kind
  if bk == () then return (∀[K] T) else none
| .tbind .allc K t => do
  let T1 <- t.infer_type G (K::Δ) Γ⟨.succ Ty⟩
  let (Tk, A, B) <- T1.is_eq_some
  let _ <- Tk.base_kind
  return ((∀[K]A) ~[Tk]~ (∀[K]B))

| _ => none

namespace Core
