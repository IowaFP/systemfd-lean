import LeanSubst
import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open LeanSubst

inductive Kinding (G : List Global) : List Kind -> Ty -> Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t#x K
| global :
  lookup_kind x G = some K ->
  Kinding G Δ gt#x K
| arrow :
  Kinding G Δ A (.base b) ->
  Kinding G Δ B ★ ->
  Kinding G Δ (A -:> B) ★
| all :
  Kinding G (K::Δ) P ★ ->
  Kinding G Δ (∀[K] P) ★
| app :
  Kinding G Δ f (A -:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f • a) B
| eq :
  Kinding G Δ A K ->
  Kinding G Δ B K ->
  Kinding G Δ (A ~[K]~ B) ★

notation:170 G:170 " ; " Δ:170 " ⊢ " A:170 " : " K:170 => Kinding G Δ A K

inductive Typing (G : List Global) : List Kind -> List Ty -> Term -> Ty -> Prop
| var :
  Γ[x]? = some A ->
  Typing G Δ Γ #x A
| global :
  lookup_type x G = some A ->
  Typing G Δ Γ g#x A
--------------------------------------------------------------------------------------
---- Matches
--------------------------------------------------------------------------------------
| mtch :
  Typing G Δ Γ (match! p s cs) A
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard :
  Typing G Δ Γ (.guard p s t) A
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  G;Δ ⊢ A : ★ ->
  Typing G Δ (A::Γ) t B ->
  Typing G Δ Γ (λ[A] t) (A -:> B)
| app :
  Typing G Δ Γ f (A -:> B) ->
  Typing G Δ Γ a A ->
  Typing G Δ Γ (f • a) B
| lamt :
  Typing G (K::Δ) Γ t P ->
  Typing G Δ Γ (Λ[K] t) (∀[K] P)
| appt :
  Typing G Δ Γ f (∀[K] P) ->
  G;Δ ⊢ a : K ->
  P' = P[su a::+0] ->
  Typing G Δ Γ (f •[a]) P'
| cast :
  Typing G Δ Γ t A ->
  Typing G Δ Γ c (A ~[K]~ B) ->
  Typing G Δ Γ (t ▹ c) B
--------------------------------------------------------------------------------------
---- Coercions
--------------------------------------------------------------------------------------
| refl :
  G;Δ ⊢ A : K ->
  Typing G Δ Γ (refl! A) (A ~[K]~ A)
| sym :
  Typing G Δ Γ t (A ~[K]~ B) ->
  Typing G Δ Γ (sym! t) (B ~[K]~ A)
| seq :
  Typing G Δ Γ t1 (A ~[K]~ B) ->
  Typing G Δ Γ t2 (B ~[K]~ C) ->
  Typing G Δ Γ (t1 `; t2) (A ~[K]~ C)
| appc :
  Typing G Δ Γ f (A ~[K1 -:> K2]~ B) ->
  Typing G Δ Γ a (C ~[K1]~ D) ->
  Typing G Δ Γ (f •c a) (A • C ~[K2]~ B • D)
| arrowc :
  Typing G Δ Γ t1 (A ~[★]~ B) ->
  Typing G Δ Γ t2 (C ~[★]~ D) ->
  Typing G Δ Γ (t1 -c> t2) (A -:> C ~[★]~ B -:> D)
| fst :
  Typing G Δ Γ t (A • C ~[K2]~ B • D) ->
  Typing G Δ Γ (fst[K1] t) (A ~[K1 -:> K2]~ B)
| snd :
  Typing G Δ Γ t (A • C ~[K2]~ B • D) ->
  Typing G Δ Γ (snd[K1] t) (C ~[K1]~ D)
| allc :
  Typing G (K::Δ) Γ t (A ~[★]~ B) ->
  Typing G Δ Γ (∀c[K] t) ((∀[K] A) ~[★]~ (∀[K] B))
| apptc :
  Typing G Δ Γ f ((∀[K] A) ~[★]~ (∀[K] B)) ->
  Typing G Δ Γ a (C ~[K]~ D) ->
  A' = A[su C::+0] ->
  B' = B[su D::+0] ->
  Typing G Δ Γ (f •c[a]) (A' ~[★]~ B')
--------------------------------------------------------------------------------------
---- Non-determinism
--------------------------------------------------------------------------------------
| zero :
  G;Δ ⊢ A : K ->
  Typing G Δ Γ `0 A
| choice :
  G;Δ ⊢ A : K ->
  Typing G Δ Γ t1 A ->
  Typing G Δ Γ t2 A ->
  Typing G Δ Γ (t1 + t2) A
