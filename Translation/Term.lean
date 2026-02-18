import Core.Ty
import Core.Term
import Surface.Ty
import Surface.Term

import Translation.Ty

def trans_term (G : List Global) (Δ : List Kind) (Γ : List Ty) : Surface.Term -> Option Term
| `#x => #x
| g`#x => g#x
| .lamt K t => do
  let K' := trans_ki K
  let t' <- trans_term G (K' :: Δ) (Γ.map (·[+1])) t
  return (Λ[K'] t')
| .lam A t => do
  let A' <- trans_ty G Δ A
  let t' <- trans_term G Δ (A' :: Γ) t
  return λ[A'] t'
| .app t1 t2 => do
  let t1' <- trans_term G Δ Γ t1
  let t2' <- trans_term G Δ Γ t2
  return (t1' • t2')
| .appt t1 t2 => do
  let t1' <- trans_term G Δ Γ t1
  let t2' <- trans_ty G Δ t2
  return (t1' •[ t2' ])
| .match (n := n) s ps cs d => do
  let s' <- trans_term G Δ Γ s
  let ops' : Vec (Option Term) n := (λ i => trans_term G Δ Γ (ps i))
  let ps' <- ops'.seq
  let ocs' : Vec (Option Term) n := (λ i => trans_term G Δ Γ (cs i))
  let cs' <- ocs'.seq
  let d' <- trans_term G Δ Γ d
  return match! s' ps' cs' d'
