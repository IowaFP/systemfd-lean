import Core.Ty
import Core.Global

import Core.Typing

open LeanSubst

namespace Core
def Kind.is_arrow : (K : Kind) -> Option (Kind × Kind)
| .arrow k1 k2 => return (k1 , k2)
| _ => none

theorem Kind.is_arrow_sound {K : Kind} :
  K.is_arrow = some (K1, K2) ->
  K = K1 -:> K2 := by
intro h
cases K <;> simp [Kind.is_arrow] at *
assumption

def Kind.base_kind : (K : Kind) -> Option Unit
| .base => some ()
| _ => none

theorem Kind.base_kind_sound : (K : Kind) ->
  K.base_kind = some b ->
  K = .base
| base => by intro; rfl
| arrow _ _ => by simp [Kind.base_kind]


-- def Kind.is_open_kind : (K : Kind) -> Option Unit
-- | ◯ => return ()
-- | _ => none

-- def Kind.is_closed_kind : (K : Kind) -> Option Unit
-- | ★ => return ()
-- | _ => none

-- theorem Kind.is_open_kind_sound :
--   k.is_open_kind = some () ->
--   k = ◯ := by
-- intro h
-- cases k; case _ k => cases k <;> simp [Kind.is_open_kind] at *
-- simp [Kind.is_open_kind] at *

-- theorem Kind.is_closed_kind_sound :
--   k.is_closed_kind = some () ->
--   k = ★ := by
-- intro h
-- cases k; case _ k => cases k <;> simp [Kind.is_closed_kind] at *
-- simp [Kind.is_closed_kind] at *


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

def Ty.valid_data (c : DataConst) (G : List Global) : Ty -> Option Unit
| A => do
  if Ty.data? c G A
  then return () else none

def Ty.kind_preamble (G : List Global) (Δ : List Kind) : List Ty -> Ty -> Option Ty
| [], τ  => return τ
| .cons a as, ∀[K] τ => do
  let K' <- a.infer_kind G Δ
  if K == K' then
    (τ[su a::+0σ]).kind_preamble G Δ as
  else none
| _ , _ => none


def spine_kinding (G : List Global) (sv : SpCtorVariant) (_ : String) (test : Ty -> Bool): SpineTy -> Option Unit
| ⟨_, Ks1, _, Ks2, _, Ts, R⟩ => do
  let Δ1 := Ks1.list
  let Δ2 := Ks2.list
  let Δ := (Δ1 ++ Δ2).reverse
  let mTKs := Ts.map (λ T : Ty => T.infer_kind G Δ)
  let TKs <- mTKs.sequence
  let RK <- R.infer_kind G Δ
  if TKs.elems_eq_to ★ && RK == ★
  then
    match sv with
    | .data _ =>
      if test R then some () else none
    | .openm =>
      let Ts' := Ts.map (λ T => T.valid_data .opn G)
      let _ <- Ts'.sequence
      if test R then return () else none
  else none

end Core
