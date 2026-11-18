import HM.Term
import HM.Ty

open LeanSubst

namespace HM

inductive Typing : List Ty -> Term -> Ty -> Prop where

def algoM (fresh : Nat) (Γ : List SchemeTy) : Term -> Ty -> Option (Subst Ty × Nat)
| .var x, expτ => do
  let scheme <- Γ[x]?
  let (fresh', infτ) := scheme.instantiate fresh
  let s <- unify' expτ infτ
  return (s, fresh')

| .lam t, expτ => do
  let Γ' := ([], .var fresh) :: Γ
  let (σ1, fresh') <- algoM (fresh + 2) Γ' t (.var (fresh + 1))
  let σ2 <- unify' expτ (.arrow (.var fresh) (.var (fresh + 1)))
  return (σ1 ∘ σ2, fresh + 2)

| .app t1 t2, expτ => do
  let (σ1, fresh') <- algoM (fresh + 1) Γ t1 (.var fresh)
  let (σ2, fresh'') <- algoM (fresh' + 1) Γ t2 (.var fresh')
  let σ := σ1 ∘ σ2
  -- fresh = fresh' -> expτ
  let σ' <- unify' (.var fresh)[σ] (.arrow (.var fresh') expτ)[σ]
  return (σ', fresh'')

| .letdef t1 t2, expτ => do
  let (σ1, fresh') <- algoM (fresh + 1) Γ t1 (.var fresh)
  let τ1 : Ty := (.var fresh)[σ1]
  let sch := τ1.generalize Γ
  let (σ2, fresh'') <- algoM fresh' (sch :: Γ) t2 expτ
  return (σ1 ∘ σ2, fresh'')

| _, _ => sorry


end HM
