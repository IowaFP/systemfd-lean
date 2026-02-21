import LeanSubst
import Core.Ty
import Core.Infer.Kind
import Core.Global

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
    .opent "Eq" (★ -:> ◯)
    , .data "Bool" ★ ([ ("True", gt#"Bool") , (("False"), gt#"Bool") ] : Vect 2 (String × Ty))
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

def Term.valid_inst_type (G : List Global)(A : Term) : Option Unit := do
  let (x, _) <- A.spine
  if is_instty G x then return () else none

def Ty.is_all_some : Ty -> Option (Kind × Ty)
| .all K B => return (K, B)
| _ => none

def Ty.is_all_some_sound {T : Ty} :
  T.is_all_some = .some (K, T1) ->
  T = ∀[K] T1 := by
intro h
cases T <;> simp [Ty.is_all_some] at *
assumption


def Ty.is_arrow_some : Ty -> Option (Ty × Ty)
| .arrow A B => return (A, B)
| _ => none

def Ty.is_arrow_some_sound {T : Ty} :
  T.is_arrow_some = .some (T1, T2) ->
  T = T1 -:> T2 := by
intro h
cases T <;> simp [Ty.is_arrow_some] at *
assumption

def Ty.is_eq_some : Ty -> Option (Kind × Ty × Ty)
| .eq K A B => return (K, A, B)
| _ => none

def Ty.is_eq_some_sound {T : Ty} :
  T.is_eq_some = some (K, A, B) ->
  T = (A ~[K]~ B) := by
intro h;
cases T <;> simp [Ty.is_eq_some] at *
assumption

def Ty.is_app_some : Ty -> Option (Ty × Ty)
| .app A B => return (A, B)
| _ => none

def Ty.is_app_some_sound {T : Ty} :
  T.is_app_some = some (A, B) ->
  T = (A • B) := by
intro h;
cases T <;> simp [Ty.is_app_some] at *
assumption


def Term.infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x => do
  let T <- Γ[x]?
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T
| g#x => do
  let T <- lookup_type G x
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T
| .match (n := n) s ps cs c => do
  let R <- s.infer_type G Δ Γ
  let _ <- R.valid_data_type G
  let ps':  Vect n (Option (String × List SpineElem)) := λ i => (ps i).spine
  let ps'' <- ps'.seq
  let vhv_pats : Vect n Bool := λ i => is_ctor G ((ps'' i).fst)
  let ctor_test := Vect.elems_eq_to true vhv_pats
  if ctor_test
  then
    let cTso : Vect n (Option Ty) :=
      λ i => (cs i).infer_type G Δ Γ
    let cTs <- cTso.seq
    let pTso : Vect n (Option Ty) :=
      λ i => (ps i).infer_type G Δ Γ
    let pTs <- pTso.seq
    let stmo : Vect n (Option Unit) := λ i => Ty.stable_type_match Δ (pTs i) R
    let _ <- stmo.seq
    let Tso : Vect n (Option Ty) :=
      λ i => Ty.prefix_type_match Δ (pTs i) (cTs i)
    let Ts : Vect n Ty <- Tso.seq
    let T <- Ts.get_elem_if_eq
    let allT <- c.infer_type G Δ Γ
    if T == allT then T else none
  else none

| .guard p s t => do
  let A <- p.infer_type G Δ Γ
  let R <- s.infer_type G Δ Γ
  let Rk <- R.infer_kind G Δ
  let _ <- Rk.is_open_kind
  let _ <- Ty.stable_type_match Δ A R
  let _ <- R.valid_open_type G
  let _ <- p.valid_inst_type G
  let B <- t.infer_type G Δ Γ
  let T <- Ty.prefix_type_match Δ A B
  let Tk <- T.infer_kind G Δ
  let _ <- Tk.base_kind
  return T

| .lam A t => do
  let Ak <- A.infer_kind G Δ
  let _ <- Ak.base_kind
  let R <- t.infer_type G Δ (A::Γ)
  let Rk <- R.infer_kind G Δ
  let _ <- Rk.base_kind
  return A -:> R
| .ctor2 (.app bk) f a => do
  let F <- f.infer_type G Δ Γ
  let (A, B) <- F.is_arrow_some
  let A' <- a.infer_type G Δ Γ
  let Ak' <- A'.infer_kind G Δ
  let bk' <- Ak'.base_kind
  if A == A' && bk == bk' then return B else none
| .tbind .lamt K t => do
  let T <- t.infer_type G (K::Δ) (Γ.map (·[+1]))
  let Tk <- (∀[K]T).infer_kind G Δ
  let bk <- Tk.base_kind
  if bk == b★ then return (∀[K] T) else none
| .ctor1 (.appt τ) t => do
  let τk <- τ.infer_kind G Δ
  let T <- t.infer_type G Δ Γ
  let (K, T) <- T.is_all_some
  if τk == K
  then return T[.su τ::+0]
  else none
| .ctor2 .cast t η => do
  let tT <- t.infer_type G Δ Γ
  let ητ <- η.infer_type G Δ Γ
  let Tk <- tT.infer_kind G Δ
  let (Tk', A, B) <- ητ.is_eq_some
  if Tk == Tk' && tT == A then return B else none
| .ctor0 (.refl A) => do
  let Ak <- A.infer_kind G Δ
  return (A ~[Ak]~ A)
| .ctor1 .sym t => do
  let T <- t.infer_type G Δ Γ
  let _ <- T.infer_kind G Δ
  let (K, A, B) <- T.is_eq_some
  return (B ~[K]~ A)
| .ctor2 .seq t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let _ <- T1.infer_kind G Δ
  let (K, A1, B1) <- T1.is_eq_some
  let T2 <- t2.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (K', A2, B2) <- T2.is_eq_some
  if K == K' && B1 == A2 then return (A1 ~[K]~ B2) else none
| .ctor2 .appc f a => do
  let T1 <- f.infer_type G Δ Γ
  let _ <- T1.infer_kind G Δ
  let (Kf, A1, B1) <- T1.is_eq_some
  let T2 <- a.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (Ka, A2, B2) <- T2.is_eq_some
  let (Kf1, Kf2) <- Kf.is_arrow
  if Ka == Kf1 then return ((A1 • A2) ~[Kf2]~ (B1 • B2)) else none
| .ctor2 .arrowc t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let _ <- T1.infer_kind G Δ
  let (Kt1, A1, B1) <- T1.is_eq_some
  let _ <- Kt1.base_kind
  let T2 <- t2.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (Kt2, A2, B2) <- T2.is_eq_some
  let bt2 <- Kt2.base_kind
  let _ <- Kt2.is_closed_kind
  return (A1 -:> A2 ~[.base bt2]~ B1 -:> B2)
| .ctor1 .fst t => do
   let T <- t.infer_type G Δ Γ
   let (K2, AC, BD) <- T.is_eq_some
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
| .ctor1 .snd t => do
   let T <- t.infer_type G Δ Γ
   let (K2, AC, BD) <- T.is_eq_some
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
| .tbind .allc K t => do
  let T1 <- infer_type G (K::Δ) (Γ.map (·[+1])) t
  let (Tk, A, B) <- T1.is_eq_some
  let _ <- Tk.is_closed_kind
  return ((∀[K]A) ~[Tk]~ (∀[K]B))
| .ctor2 .apptc f a => do
  let Tf <- infer_type G Δ Γ f
  let (KTf, aAf, aBf) <- Tf.is_eq_some
  let (KA, A) <- aAf.is_all_some
  let (KB, B) <- aBf.is_all_some
  let Ta <- infer_type G Δ Γ a
  let (KTa, Aa, Ba) <- Ta.is_eq_some
  if KA == KB && KTa == KA && KTf == ★
  then return (A[.su Aa::+0:Ty] ~[★]~ B[.su Ba::+0:Ty])
  else none
| .ctor2 .choice t1 t2 => do
  let T1 <- infer_type G Δ Γ t1
  let T2 <- infer_type G Δ Γ t2
  let _ <- T1.infer_kind G Δ
  if T1 == T2 then return T1 else none
| _ => none

namespace Core
