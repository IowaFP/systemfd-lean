import Core.Ty
import Core.Algorithm.Kind
import Core.Global

def infer_type (G : List Global) (Δ : List Kind) (Γ : List Ty) : Term -> Option Ty
| #x =>  Γ[x]?
| g#x => lookup_type G x
| _ => sorry
