import LeanSubst
import Core.Ty
import Core.Infer.Kind
import Core.Global
import Core.Vec
import Lilac

open LeanSubst
namespace Core
-- A is the type of the pattern
-- and is of the form ∀[★]∀[★] x -t> y -t> ... -t> T p q r
-- R is the type of the scrutinee
-- and is of the form T' p' q' r'
-- we need to make sure T == T' (i.e. it is a datatype or an opent)
def Ty.stable_type_match : List Kind -> Ty -> Ty -> Option Unit
| Δ, (Ty.all K A), R => Ty.stable_type_match (K::Δ) A R[+1]
| Δ, (Ty.arrow _ B), R => Ty.stable_type_match Δ B R
| _, (Ty.eq _ _ _ ), _ => none
| _, A, R =>
 do
  let _ <- R.spine
  if A == R -- && (is_opent G x || is_data G x)
  then some ()
  else none

namespace Infer.Ty.Test

def G : List Global := [
    .opent "Eq" (★ -:> ★)
  , .data 2 "Bool" ★ (("True", gt#"Bool") :: (("False"), gt#"Bool") :: .nil)
  ]


def R : Ty := gt#"Eq" • t#0
def A : Ty := (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)

#eval A.stable_type_match [] R

#guard R.spine == .some ("Eq", [t#0])

end Infer.Ty.Test



-- A is the type of the pattern and has the form
-- ∀[★]∀[★].. x -t> y -t> T p q r
-- T is the type of the rhs of the branch and has the form
-- ∀[★]∀[★].. x' -t> y' -t> ... z -t> T' p' q' r'
-- A potentially has more ∀s and -t> s than in the branch
-- This function returns the 'extra' bits
def Ty.prefix_type_match (Δ : List Kind) : Ty -> Ty -> Option Ty
  | (.arrow A B), (.arrow A' B') => do
    if A == A'
    then prefix_type_match Δ B B'
    else none

  | (.all K A), (.all K' A') => do
    if K == K'
    then let x <- prefix_type_match (K :: Δ) A A'
         if x[-1][+1] == x
         then return x[-1]
         else none
    else none
  | A, T => do
    let _ <- A.spine
    return T

def Ty.valid_open_type (G : List Global) (A : Ty) : Option Unit := do
  let (x, _) <- A.spine
  if is_opent G x
  then return () else none

def Ty.valid_data_type (G : List Global) (A : Ty) : Option Unit := do
  let (x, _) <- A.spine
  if is_data G x
  then return () else none

-- def Term.valid_inst_type (G : List Global)(A : Term) : Option Unit := do
--   let (x, _) <- A.spine
--   if is_instty G x then return () else none

def Ty.kind_preamble (G : List Global) (Δ : List Kind) : List Ty -> Ty -> Option Ty
| [], τ  => return τ
| .cons a as, ∀[K] τ => do
  let K' <- a.infer_kind G Δ
  if K == K' then
    (τ[su a :: +0]).kind_preamble G Δ as
  else none
| _ , _ => none

def Term.infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x => do
  let T <- Γ[x]?
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T
| .defn x => do
  let T <- lookup_type G x
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T
| spctor (n := n) .cdata x τs ts => do
  let D1 <- lookup_spctor_type G x
  let D2 <- D1.kind_preamble G Δ τs
  let (Ts, D3) <- Ty.typescope n D2
  let mτs : Lilac.Vec (Option Ty) n := Lilac.Fun.Vec.to ((λ t => infer_type G Δ Γ t) <$> ts)
  let τs <- mτs.seq
  let mbs := (Ts.zip τs).fold true (λ p acc => p.fst == p.snd && acc)
  if mbs then return D3 else none
| .mtch m n _ _ _  => do

  none
| .cast τ c t => do
  let e <- c.infer_type G Δ Γ
  let (K, A, B) <- e.is_eq_some
  let τK <- τ.infer_kind G (K :: Δ)
  let _ <- τK.base_kind
  let tA <- t.infer_type G Δ Γ
  if τ[su A::+0] == tA then return τ[su B::+0] else .none
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
  let (Kf, A1, B1) <- T1.is_eq_some
  let T2 <- a.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (Ka, A2, B2) <- T2.is_eq_some
  let (Kf1, Kf2) <- Kf.is_arrow
  if Ka == Kf1 then return ((A1 • A2) ~[Kf2]~ (B1 • B2)) else none
| .ctor2 .app f a => do
  let F <- f.infer_type G Δ Γ
  let (A, B) <- F.is_arrow_some
  let A' <- a.infer_type G Δ Γ
  let Ak' <- A'.infer_kind G Δ
  let _ <- Ak'.base_kind
  if A == A' then return B else none

| .tbind .lamt K t => do
  let T <- t.infer_type G (K::Δ) (Γ.map (·[+1]))
  let Tk <- (∀[K]T).infer_kind G Δ
  let bk <- Tk.base_kind
  if bk == () then return (∀[K] T) else none
| .tbind .allc K t => do
  let T1 <- infer_type G (K::Δ) (Γ.map (·[+1])) t
  let (Tk, A, B) <- T1.is_eq_some
  let _ <- Tk.base_kind
  return ((∀[K]A) ~[Tk]~ (∀[K]B))
| _ => none

namespace Core
