import Core.Ty
import Core.Global

@[simp]
def wf_kind : (K : Kind) -> Option Unit
| ★ => return ()
| ◯ => return ()
| .arrow k1 k2 => do
  _ <- wf_kind k1
  _ <- wf_kind k2
  return ()

def Kind.is_arrow : (K : Kind) -> Option (Kind × Kind)
| .arrow k1 k2 => return (k1 , k2)
| _ => none

def Kind.base_kind : (K : Kind) -> Option BaseKind
| ★ => return b★
| ◯ => return b◯
| _ => none

@[simp]
def infer_kind (G : List Global) (Δ : List Kind) : Ty -> Option Kind
| t#x => do
  let T <- Δ[x]?
  let _ <- wf_kind T
  return T
| gt#x => do
  let T <- lookup_kind G x
  let _ <- wf_kind T
  return T
| .arrow b t1 t2 => do
  let k1 <- infer_kind G Δ t1
  let _ <- wf_kind k1
  let b1 <- k1.base_kind
  let k2 <- infer_kind G Δ t2
  let _ <- k2.base_kind
  let _ <- wf_kind k2
  if b == b1 then return k2 else none
| .all K t => do
  let _ <- wf_kind K
  let tk <- infer_kind G (K :: Δ) t
  let _ <- wf_kind tk
  if tk == ★ then return ★ else none
| .eq K A B => do
  let _ <- wf_kind K
  let Ak <- infer_kind G Δ A
  let Bk <- infer_kind G Δ B
  if Ak == Bk && Ak == K then return ★ else none
| .app A B => do
  let Ak <- infer_kind G Δ A
  let _ <- wf_kind Ak
  let Bk <- infer_kind G Δ B
  let _ <- wf_kind Bk
  let (k1, k2) <- Ak.is_arrow
  if k1 == Bk then return k2 else none
