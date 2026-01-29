import LeanSubst
import Core.Ty
import Core.Infer.Kind
import Core.Global

-- open LeanSubst
-- A is the type of the pattern
-- and is of the form ∀[★]∀[★] x -t> y -t> ... -t> T p q r
-- R is the type of the scrutinee
-- and is of the form T' p' q' r'
-- we need to make sure T == T' (i.e. it is a datatype or an opent)
def Ty.stable_type_match (G : List Global) : Ty -> Ty -> Option Unit
| (Ty.all K A), (Ty.all K' R) =>
  if K == K'
  then Ty.stable_type_match G A R
  else none
| A, R =>
 do
  let (tele, sR) := A.telescope
  let (x, _) <- R.spine
  if R[λ x => .re (x + tele.count_binders)] == sR && (is_opent G x || is_data G x)
  then some ()
  else none

namespace Infer.Type.Test

def G : List Global := [
    .opent "Eq" (★ -:> ◯)
    , .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]
  ]


def R : Ty := gt#"Eq" • t#0
def A : Ty := (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)

#eval A.stable_type_match G R
def ATele := A.telescope.1
def sR := A.telescope.2

#eval R.spine
#eval is_opent G "Eq"
#eval ATele.count_binders
#eval R[λ x => .re (x + ATele.count_binders)] == sR

end Infer.Type.Test



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
         if x[λ x => .re (x - 1)][λ x => .re (x + 1)] == x
         then return x[λ x => .re (x - 1)]
         else none
    else none
  | A, T => do
    let _ <- A.spine
    return T

def Ty.valid_open_type (G : List Global) : (T : Ty) -> Option Unit
| .arrow _ B => valid_open_type G B
| .all _ B => valid_open_type G B
| A => do let (x, _) <- A.spine
          if is_opent G x
           then return () else none

def Ty.valid_data_type (G : List Global) : (T : Ty) -> Option Unit
| .arrow _ B => valid_open_type G B
| .all _ B => valid_open_type G B
| A => do let (x, _) <- A.spine
          if is_data G x
          then return () else none

def Term.valid_inst_type (G : List Global) : (A : Term) -> Option Unit := λ A =>
  do let (x, _) <- A.spine
     if is_instty G x then return () else none

def Ty.is_all_some : Ty -> Option (Kind × Ty)
| .all K B => return (K, B)
| _ => none


def Ty.is_arrow_some : Ty -> Option (Ty × Ty)
| .arrow A B => return (A, B)
| _ => none

def Ty.is_eq_some : Ty -> Option (Kind × Ty × Ty)
| .eq K A B => return (K, A, B)
| _ => none

def Ty.is_app_some : Ty -> Option (Ty × Ty)
| .app A B => return (A, B)
| _ => none

def Term.infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x =>  Γ[x]?
| g#x => lookup_type G x
| .match (n := n + 1) s ps cs => do
  let R <- s.infer_type G Δ Γ
  let _ <- R.valid_data_type G
  let (dt, _) <- R.spine
  let ps':  Vec (Option (String × List SpineElem)) (n + 1) := λ i => (ps i).spine
  let ps'' <- ps'.seq
  let vhv_pats : Vec Bool (n + 1) := λ i => is_ctor G ((ps'' i).fst)
  let ctor_test := Vec.elems_eq_to true vhv_pats
  if ctor_count dt G == some (n + 1) && ctor_test
  then
    let cTs : Vec (Option Ty) (n + 1) :=
      λ i => (cs i).infer_type G Δ Γ
    let pTs : Vec (Option Ty) (n + 1) :=
      λ i => (ps i).infer_type G Δ Γ
    let Tso : Vec (Option Ty) (n + 1) :=
      λ i => do let cT <- cTs i
                let pT <- pTs i
                let _ <- Ty.stable_type_match G pT R
                Ty.prefix_type_match Δ pT cT

    let Ts : Vec Ty (n + 1) <- Tso.seq
    Ts.get_elem_if_eq
  else none

| .guard p s t => do
  let A <- p.infer_type G Δ Γ
  let R <- s.infer_type G Δ Γ
  let Rk <- R.infer_kind G Δ
  let _ <- Rk.is_open_kind
  let _ <- Ty.stable_type_match G A R
  let (ph, _) <- p.spine
  let _ <- R.valid_open_type G
  let _ <- p.valid_inst_type G
  let B <- t.infer_type G Δ Γ
  let T <- Ty.prefix_type_match Δ A B
  let Tk <- T.infer_kind G Δ
  return T

| .lam A t => do
  let R <- t.infer_type G Δ (A::Γ)
  let _ <- R.infer_kind G Δ
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
  return (∀[K] T)
| .ctor1 (.appt τ) t => do
  let _ <- τ.infer_kind G Δ
  let T <- t.infer_type G Δ Γ
  let (_, T) <- T.is_all_some
  return T[.su τ::+0]
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
  let Tk <- T.infer_kind G Δ
  let (K, A, B) <- T.is_eq_some
  return (B ~[K]~ A)
| .ctor2 .seq t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let T1k <- T1.infer_kind G Δ
  let (K, A1, B1) <- T1.is_eq_some
  let T2 <- t2.infer_type G Δ Γ
  let T2k <- T2.infer_kind G Δ
  let (K', A2, B2) <- T2.is_eq_some
  if K == K' && B1 == A2 then return (A1 ~[K]~ B2) else none
| .ctor2 .appc f a => do
  let T1 <- f.infer_type G Δ Γ
  let T1k <- T1.infer_kind G Δ
  let (Kf, A1, B1) <- T1.is_eq_some
  let T2 <- a.infer_type G Δ Γ
  let T2k <- T2.infer_kind G Δ
  let (Ka, A2, B2) <- T2.is_eq_some
  let (Kf1, Kf2) <- Kf.is_arrow
  if Ka == Kf1 then return ((A1 • A2) ~[Kf2]~ (B1 • B2)) else none
| .ctor2 .arrowc t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let _ <- T1.infer_kind G Δ
  let (Kt1, A1, B1) <- T1.is_eq_some
  let bt1 <- Kt1.base_kind
  let T2 <- t2.infer_type G Δ Γ
  let _ <- T2.infer_kind G Δ
  let (Kt2, A2, B2) <- T2.is_eq_some
  let bt2 <- Kt2.base_kind
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
  let Tbk <- Tk.base_kind
  return (∀[K]A ~[.base Tbk]~ ∀[K]B)
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
  if T1 == T2 then return T1 else none
| _ => none
