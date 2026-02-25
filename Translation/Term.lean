import Core.Ty
import Core.Term
import Surface.Ty
import Surface.Term

import Translation.Ty

@[simp, grind]
def Surface.Term.translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
  Surface.Term -> Option Core.Term
| `#x => #x
| g`#x => g#x
| .lamt K t => do
  let t' <- t.translate G (K.translate :: Δ) (Γ.map (·[+1]))
  return (Λ[K.translate] t')
| .lam A t => do
  let t' <- t.translate G Δ (A.translate :: Γ)
  return λ[A.translate] t'
| .app t1 t2 => do
  let t1' <- t1.translate G Δ Γ
  let t2' <- t2.translate G Δ Γ
  return (t1' • t2')
| .appt t1 t2 => do
  let t1' <- t1.translate G Δ Γ
  let t2' <- t2.translate
  return (t1' •[ t2' ])
| .match (n := n) s ps cs d => do
  let s' <- s.translate G Δ Γ
  let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
  let ps' <- ops'.seq
  let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
  let cs' <- ocs'.seq
  let d' <- d.translate G Δ Γ
  return match! n s' ps' cs' d'



-- @[simp, grind]
def Surface.Term.type_directed_translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Core.Ty):
  Surface.Term -> Option Core.Term
| `#x =>
  if Γ[x]? == some τ then return #x else none
| .lamt K t => do
  let (K', τ') <- τ.is_all_some
  let t' <- t.type_directed_translate G (K.translate :: Δ) (Γ.map (·[+1])) τ'
  if K' == K.translate then return (Λ[K.translate] t') else none
| .lam A t => do
  let (A', B') <- τ.is_arrow_some
  let t' <- t.type_directed_translate G Δ (A.translate :: Γ) B'
  if A' == A.translate
  then return λ[A.translate] t' else none

-- Elimination forms are a little annoying
| .match (n := n) s ps cs d => do -- also maybe store the type of the scrutinee to eliminate
  let s' <- s.translate G Δ Γ
  let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
  let ps' <- ops'.seq
  let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
  let cs' <- ocs'.seq
  let d' <- d.type_directed_translate G Δ Γ τ
  return match! n s' ps' cs' d'
-- | .app t1 t2 => do
--   let t1' <- t1.translate G Δ Γ
--   let t2' <- t2.translate G Δ Γ
--   return (t1' • t2')
-- | .appt t1 t2 => do
--   let t1' <- t1.translate G Δ Γ
--   let t2' <- t2.translate
--   return (t1' •[ t2' ])
| t => do
  let (x, sp) <- t.spine
  let hτ <- Core.lookup_type G x
  let (argτs, r) := hτ.telescope
  let app <- List.foldlM (λ (hτ, acct, τ) x =>
               match τ, sp with
               | .nil, _ => if sp.isEmpty then return (hτ, acct, τ) else none -- cannot apply more arguments
               | .kind K te, (.cons (.type t) tl) => do
                 return (hτ, acct •[t.translate], te)
               | .ty T te, (.cons (.term t) tl) =>  do
                 let t' <- t.type_directed_translate G Δ Γ T
                 return (hτ, acct • t', te)
               | _ , _ => none)
               (hτ, g#x, argτs) sp
  if r == τ then return app.2.1 else none
termination_by t => t.size
decreasing_by (repeat sorry)
