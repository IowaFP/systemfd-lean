import LeanSubst
import Core.Vec

import Surface.Ty
import Surface.Term
import Surface.Global

def Surface.ValidHeadVariable (t : Term) (test : String -> Bool) : Prop :=
  ∃ x, Term.spine t = some x ∧ test x.fst

def Surface.ValidTyHeadVariable (t : Ty) (test : String -> Bool) : Prop :=
  ∃ x, Ty.spine t = some x ∧ test x.fst

inductive Surface.StableTypeMatch : List Kind -> Ty -> Ty -> Prop
| refl :
  Ty.spine R = some x ->
  StableTypeMatch Δ R R
| arrow :
  StableTypeMatch Δ B R ->
  StableTypeMatch Δ (A `-:> B) R
| all :
  StableTypeMatch (K::Δ) B R[+1] ->
  StableTypeMatch Δ (`∀[K] B) R


inductive Surface.PrefixTypeMatch : List Kind -> Ty -> Ty -> Ty -> Prop
| refl :
  Ty.spine B = some x ->
  PrefixTypeMatch Δ B T T
| arrow :
  PrefixTypeMatch Δ B V T ->
  PrefixTypeMatch Δ (A `-:> B) (A `-:> V) T
| all :
  PrefixTypeMatch (K::Δ) B V T[+1] ->
  PrefixTypeMatch Δ (`∀[K] B) (`∀[K] V) T


inductive Surface.Kinding (G : List Surface.Global) : List Surface.Kind -> Surface.Ty -> Surface.Kind -> Prop
| var :
  Δ[x]? = some K ->
  Surface.Kinding G Δ t`#x K
| global :
  Surface.lookup_kind G x = some K ->
  Kinding G Δ gt`#x K
| arrow :
  Surface.Kinding G Δ A (.base b1) ->
  Surface.Kinding G Δ B (.base b2) ->
  Surface.Kinding G Δ (A `-:> B) `★
| all :
  Surface.Kinding G (K::Δ) P `★ ->
  Surface.Kinding G Δ (`∀[K] P) `★
| app :
  Surface.Kinding G Δ f (A `-:> B) ->
  Surface.Kinding G Δ a A ->
  Surface.Kinding G Δ (f `• a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Surface.Kinding G Δ A K

inductive Surface.Typing (G : List Surface.Global) :
  List Surface.Kind -> List Surface.Ty -> Surface.Term -> Surface.Ty -> Prop
| var :
  Γ[x]? = some A ->
  G&Δ ⊢s A : .base b ->
  Typing G Δ Γ `#x A
| global :
  lookup_type G x = some A ->
  G&Δ ⊢s A : .base b ->
  Typing G Δ Γ g`#x A
--------------------------------------------------------------------------------------
---- Matches
--------------------------------------------------------------------------------------
| mtch (CTy : Fin n -> Ty)
       (PTy : Fin n -> Ty)
       (pats : Vec Term n)
       (cs : Vec Term n) :
  Typing G Δ Γ s R ->
  ValidTyHeadVariable R (is_data G) ->
  Typing G Δ Γ c T -> -- catch all term is of type T
  (∀ i, ValidHeadVariable (pats i) (is_ctor G)) -> -- patterns are of the right shape
  (∀ i, Typing G Δ Γ (pats i) (PTy i)) -> -- each pattern has a type
  (∀ i, StableTypeMatch Δ (PTy i) R) -> -- the pattern type has a return type that matches datatype
  (∀ i, Typing G Δ Γ (cs i) (CTy i)) -> -- each case match has a type
  (∀ i, PrefixTypeMatch Δ (PTy i) (CTy i) T) -> -- patten type and case type
  Typing G Δ Γ (matchˢ! s pats cs c) T
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  G&Δ ⊢s A : .base b ->
  Typing G Δ (A::Γ) t B ->
  Typing G Δ Γ (λˢ[A] t) (A `-:> B)
| app :
  G&Δ ⊢s A : .base b ->
  Typing G Δ Γ f (A `-:> B) ->
  Typing G Δ Γ a A ->
  Typing G Δ Γ (f `• a) B
| lamt :
  Kinding G Δ (`∀[K]P) `★ ->
  Typing G (K::Δ) (Γ.map (·[+1])) t P ->
  Typing G Δ Γ (Λˢ[K] t) (`∀[K] P)
| appt :
  Typing G Δ Γ f (`∀[K] P) ->
  G&Δ ⊢s a : K ->
  P' = P[.su a :: +0:Surface.Ty] ->
  Typing G Δ Γ (f `•[a]) P'

notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " : " A:170 => Surface.Typing G Δ Γ t A
