import LeanSubst
import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open LeanSubst

def ValidHeadVariable (t : Term) (test : String -> Bool) : Prop :=
  ∃ x, some x = Term.spine t ∧ test x.fst

def ValidTyHeadVariable (t : Ty) (test : String -> Bool) : Prop :=
  ∃ x, some x = Ty.spine t ∧ test x.fst

inductive StableTypeMatch : List Kind -> Ty -> Ty -> Prop
| refl :
  some x = Ty.spine R ->
  StableTypeMatch Δ R R
| arrow :
  StableTypeMatch Δ B R ->
  StableTypeMatch Δ (A -:> B) R
| all :
  StableTypeMatch (K::Δ) B R[+1] ->
  StableTypeMatch Δ (∀[K] B) R

inductive PrefixTypeMatch : List Kind -> Ty -> Ty -> Ty -> Prop
| refl :
  some x = Ty.spine B ->
  PrefixTypeMatch Δ B T T
| arrow :
  PrefixTypeMatch Δ B V T ->
  PrefixTypeMatch Δ (A -:> B) (A -:> V) T
| all :
  PrefixTypeMatch (K::Δ) B V T[+1] ->
  PrefixTypeMatch Δ (∀[K] B) (∀[K] V) T

inductive Kinding (G : List Global) : List Kind -> Ty -> Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t#x K
| global :
  lookup_kind G x = some K ->
  Kinding G Δ gt#x K
| arrow :
  Kinding G Δ A (.base b1) ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A -[b1]> B) (.base b2)
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
  G;Δ ⊢ A : K ->
  Typing G Δ Γ #x A
| global :
  lookup_type G x = some A ->
  G;Δ ⊢ A : K ->
  Typing G Δ Γ g#x A
--------------------------------------------------------------------------------------
---- Matches
--------------------------------------------------------------------------------------
| mtch (cs : Vec Term (n + 1)) :
  Typing G Δ Γ s R ->
  (∀ i, Typing G Δ Γ (cs i) T) ->
  ValidTyHeadVariable R (is_data G) ->
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  Typing G Δ Γ (match! s cs) T
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard :
  Typing G Δ Γ p A ->
  Typing G Δ Γ s R ->
  Typing G Δ Γ t B ->
  ValidHeadVariable p (is_instty G) ->
  ValidTyHeadVariable R (is_opent G) ->
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  Typing G Δ Γ (.guard p s t) T
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  G;Δ ⊢ A : .base b ->
  Typing G Δ (A::Γ) t B ->
  Typing G Δ Γ (λ[b,A] t) (A -:> B)
| app :
  Typing G Δ Γ f (A -[b]> B) ->
  Typing G Δ Γ a A ->
  Typing G Δ Γ (f •(b) a) B
| lamt :
  Typing G (K::Δ) (Γ.map (·[+1])) t P ->
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
  G;Δ ⊢ C : K1 ->
  G;Δ ⊢ D : K1 ->
  Typing G Δ Γ t (A • C ~[K2]~ B • D) ->
  Typing G Δ Γ (fst! t) (A ~[K1 -:> K2]~ B)
| snd :
  G;Δ ⊢ C : K1 ->
  G;Δ ⊢ D : K1 ->
  Typing G Δ Γ t (A • C ~[K2]~ B • D) ->
  Typing G Δ Γ (snd! t) (C ~[K1]~ D)
| allc :
  Typing G (K::Δ) (Γ.map (·[+1])) t (A ~[★]~ B) ->
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
  Typing G Δ Γ (t1 `+ t2) A

notation:170 G:170 " ; " Δ:170 " ; " Γ:170 " ⊢ " t:170 " : " A:170 => Typing G Δ Γ t A
