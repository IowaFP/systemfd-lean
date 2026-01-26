import Core.Ty
import Core.Algorithm.Kind
import Core.Global



def Ty.is_all_some : Ty -> Option (Kind × Ty)
| .all K B => return (K, B)
| _ => none


def Ty.is_arrow_some : Ty -> Option (BaseKind × Ty × Ty)
| .arrow b A B => return (b, A, B)
| _ => none

def Ty.is_eq_some : Ty -> Option (Kind × Ty × Ty)
| .eq K A B => return (K, A, B)
| _ => none

def Ty.is_app_some : Ty -> Option (Ty × Ty)
| .app A B => return (A, B)
| _ => none

def Ty.stable_type_match (Δ : List Kind) (A : Ty) (R : Ty) : Option Unit := none
def Ty.prefix_type_match (Δ : List Kind) (A B : Ty) : Option Ty := none


def Term.infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x =>  Γ[x]?
| g#x => lookup_type G x
| .match (n := n + 1) s ps cs => do
  let R <- s.infer_type G Δ Γ
  let (dt, _) <- R.spine
  let Tso := Vec.map2 ps cs (λ p c => do
    let B <- ctor_ty p G
    let A <- c.infer_type G Δ Γ
    let _ <- Ty.stable_type_match Δ B R
    let T <- Ty.prefix_type_match Δ A B
    return T
    )
  let Ts <- Tso.seq
  -- TODO: check that each element of Ts is equal

  none
  -- let Ts := cs.fold (λ acc c =>
  --   none
  --   ) (v[])
| .guard p s t => do
  none
| .lam b A t => do
  let R <- t.infer_type G Δ (A::Γ)
  let _ <- R.infer_kind G Δ
  return A -[b]> R
| .ctor2 (.app bk) a b => do
  let A <- infer_type G Δ Γ a
  let (bk', B, R) <- A.is_arrow_some
  let B' <- b.infer_type G Δ Γ
  if B == B' && bk == bk' then return R else none
| .ctor1 (.appt τ) t => do
  let τk <- τ.infer_kind G Δ
  let _ <- wf_kind τk
  let T <- t.infer_type G (τk :: Δ) (Γ.map (·[+1]))
  return ∀[τk] T
| .ctor2 .cast t η => do
  let tT <- t.infer_type G Δ Γ
  let ητ <- η.infer_type G Δ Γ
  let Tk <- tT.infer_kind G Δ
  let (Tk', A, B) <- ητ.is_eq_some
  if Tk == Tk' && tT == A then return B else none
| .ctor0 (.refl A) => do
  let Ak <- A.infer_kind G Δ
  let _ <- wf_kind Ak
  return A
| .ctor1 .sym t => do
  let T <- t.infer_type G Δ Γ
  let Tk <- T.infer_kind G Δ
  _ <- wf_kind Tk
  let (K, A, B) <- T.is_eq_some
  return (B ~[K]~ A)
| .ctor2 .seq t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let T1k <- T1.infer_kind G Δ
  _ <- wf_kind T1k
  let (K, A1, B1) <- T1.is_eq_some
  let T2 <- t2.infer_type G Δ Γ
  let T2k <- T2.infer_kind G Δ
  _ <- wf_kind T2k
  let (K', A2, B2) <- T2.is_eq_some
  if K == K' && B1 == A2 then return (A1 ~[K]~ B2) else none
| .ctor2 .appc f a => do
  let T1 <- f.infer_type G Δ Γ
  let T1k <- T1.infer_kind G Δ
  _ <- wf_kind T1k
  let (Kf, A1, B1) <- T1.is_eq_some
  let T2 <- a.infer_type G Δ Γ
  let T2k <- T2.infer_kind G Δ
  _ <- wf_kind T2k
  let (Ka, A2, B2) <- T2.is_eq_some
  let (Kf1, Kf2) <- Kf.is_arrow
  if Ka == Kf1 then return ((A1 • A2) ~[Kf2]~ (B1 • B2)) else none
| .ctor2 .arrowc t1 t2 => do
  let T1 <- t1.infer_type G Δ Γ
  let T1k <- T1.infer_kind G Δ
  _ <- wf_kind T1k
  let (Kt1, A1, B1) <- T1.is_eq_some
  let bt1 <- Kt1.base_kind
  let T2 <- t2.infer_type G Δ Γ
  let T2k <- T2.infer_kind G Δ
  _ <- wf_kind T2k
  let (Kt2, A2, B2) <- T2.is_eq_some
  let bt2 <- Kt2.base_kind
  return (A1 -[bt1]> A2 ~[.base bt2]~ B1 -[bt1]> B2)
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
  let _ <- wf_kind Tk
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
decreasing_by repeat sorry
