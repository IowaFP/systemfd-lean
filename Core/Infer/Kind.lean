import Core.Ty
import Core.Global

def Kind.is_arrow : (K : Kind) -> Option (Kind × Kind)
| .arrow k1 k2 => return (k1 , k2)
| _ => none

theorem Kind.is_arrow_sound {K : Kind} :
  K.is_arrow = some (K1, K2) ->
  K = K1 -:> K2 := by
intro h
cases K <;> simp [Kind.is_arrow] at *
assumption

def Kind.base_kind : (K : Kind) -> Option BaseKind
| ★ => return b★
| ◯ => return b◯
| _ => none

theorem Kind.base_kind_sound {K : Kind} :
  K.base_kind = some b ->
  K = .base b := by
intro h
cases K <;> simp [Kind.base_kind] at *
case _ a =>
  cases a <;> simp at *
  assumption; assumption


def Kind.is_open_kind : (K : Kind) -> Option Unit
| ◯ => return ()
| _ => none

def Kind.is_closed_kind : (K : Kind) -> Option Unit
| ★ => return ()
| _ => none

theorem Kind.is_open_kind_sound :
  k.is_open_kind = some () ->
  k = ◯ := by
intro h
cases k; case _ k => cases k <;> simp [Kind.is_open_kind] at *
simp [Kind.is_open_kind] at *

theorem Kind.is_closed_kind_sound :
  k.is_closed_kind = some () ->
  k = ★ := by
intro h
cases k; case _ k => cases k <;> simp [Kind.is_closed_kind] at *
simp [Kind.is_closed_kind] at *


@[simp]
def Ty.infer_kind (G : List Global) (Δ : List Kind) : Ty -> Option Kind
| t#x => do
  let T <- Δ[x]?
  return T
| gt#x => do
  let T <- lookup_kind G x
  return T
| .arrow t1 t2 => do
  let k1 <- infer_kind G Δ t1
  let _ <- k1.base_kind
  let k2 <- infer_kind G Δ t2
  let _ <- k2.base_kind
  return ★
| .all K t => do
  let tk <- infer_kind G (K :: Δ) t
  if tk == ★ then return ★ else none
| .eq K A B => do
  let Ak <- infer_kind G Δ A
  let Bk <- infer_kind G Δ B
  if Ak == Bk && Ak == K then return ★ else none
| .app A B => do
  let Ak <- infer_kind G Δ A
  let Bk <- infer_kind G Δ B
  let (k1, k2) <- Ak.is_arrow
  if k1 == Bk then return k2 else none
