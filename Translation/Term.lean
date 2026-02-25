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
