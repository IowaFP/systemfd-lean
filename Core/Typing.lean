import LeanSubst
import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open LeanSubst

def ValidHeadVariable (t : Term) (test : String -> Bool) : Prop :=
  ∃ x, Term.spine t = some x ∧ test x.fst

def ValidTyHeadVariable (t : Ty) (test : String -> Bool) : Prop :=
  ∃ x, Ty.spine t = some x ∧ test x.fst

inductive StableTypeMatch : List Kind -> Ty -> Ty -> Prop
| refl :
  Ty.spine R = some x ->
  StableTypeMatch Δ R R
| arrow :
  StableTypeMatch Δ B R ->
  StableTypeMatch Δ (A -:> B) R
| all :
  StableTypeMatch (K::Δ) B R[+1] ->
  StableTypeMatch Δ (∀[K] B) R

inductive PrefixTypeMatch : List Kind -> Ty -> Ty -> Ty -> Prop
| refl :
  Ty.spine B = some x ->
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

notation:170 G:170 "&" Δ:170 " ⊢ " A:170 " : " K:170 => Kinding G Δ A K

inductive Typing (G : List Global) : List Kind -> List Ty -> Term -> Ty -> Prop
| var :
  Γ[x]? = some A ->
  G&Δ ⊢ A : .base b ->
  Typing G Δ Γ #x A
| global :
  lookup_type G x = some A ->
  G&Δ ⊢ A : .base b ->
  Typing G Δ Γ g#x A
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
  Typing G Δ Γ (match! s pats cs c) T
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
  G&Δ ⊢ A : .base b ->
  Typing G Δ (A::Γ) t B ->
  Typing G Δ Γ (λ[A] t) (A -:> B)
| app :
  G&Δ ⊢ A : .base b ->
  Typing G Δ Γ f (A -:> B) ->
  Typing G Δ Γ a A ->
  Typing G Δ Γ (f •(b) a) B
| lamt :
  Kinding G Δ (∀[K]P) ★ ->
  Typing G (K::Δ) (Γ.map (·[+1])) t P ->
  Typing G Δ Γ (Λ[K] t) (∀[K] P)
| appt :
  Typing G Δ Γ f (∀[K] P) ->
  G&Δ ⊢ a : K ->
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
  G&Δ ⊢ A : K ->
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
  Typing G Δ Γ (f •c a) ((A • C) ~[K2]~ (B • D))
| arrowc :
  Typing G Δ Γ t1 (A ~[.base b1]~ B) ->
  Typing G Δ Γ t2 (C ~[.base b2]~ D) ->
  Typing G Δ Γ (t1 -c> t2) ((A -:> C) ~[★]~ (B -:> D))
| fst :
  G&Δ ⊢ C : K1 ->
  G&Δ ⊢ D : K1 ->
  Typing G Δ Γ t ((A • C) ~[K2]~ (B • D)) ->
  Typing G Δ Γ (fst! t) (A ~[K1 -:> K2]~ B)
| snd :
  G&Δ ⊢ C : K1 ->
  G&Δ ⊢ D : K1 ->
  Typing G Δ Γ t ((A • C) ~[K2]~ (B • D)) ->
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
  G&Δ ⊢ A : .base b ->
  Typing G Δ Γ `0 A
| choice :
  G&Δ ⊢ A : K ->
  Typing G Δ Γ t1 A ->
  Typing G Δ Γ t2 A ->
  Typing G Δ Γ (t1 `+ t2) A

notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢ " t:170 " : " A:170 => Typing G Δ Γ t A

inductive ValidCtor (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidCtor x T
| all :
  ValidCtor x P ->
  ValidCtor x (∀[K] P)
| arrow :
  ValidCtor x B ->
  ValidCtor x (A -:> B)

inductive ValidOpenKind : Kind -> Prop where
| base : ValidOpenKind ◯
| arrow : ValidOpenKind B -> ValidOpenKind (A -:> B)

inductive ValidInstTy (G : List Global) (x : String) : List Kind -> Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  G&Δ ⊢ T : ◯ ->
  ValidInstTy G x Δ T
| all :
  G& (K::Δ) ⊢ T : ★ ->
  ValidInstTy G x (K::Δ) T ->
  ValidInstTy G x Δ (∀[K] T)
| arrow :
  ValidInstTy G x Δ T ->
  G&Δ ⊢ A : .base b ->
  ValidInstTy G x Δ (A -:> T)

inductive GlobalWf : List Global -> Global -> Prop where
| data {ctors : Vec (String × Ty) n} {ctors' : Vec String n}:
  (∀ i y T, ctors i = (y, T) ->
    (.data x K v[]::G)&[] ⊢ T : ★ ∧
     ValidCtor x T ∧
     none = lookup y (.data x K v[]::G)) ->
  (ctors' = λ i => (ctors i).1) ->
   ctors'.HasUniqueElems ->
  lookup x G = none ->
  GlobalWf G (.data x K ctors)
| opent :
  ValidOpenKind K ->
  lookup x G = none ->
  GlobalWf G (.opent x K)
| openm :
  G&[] ⊢ T : .base b ->
  lookup x G = none ->
  GlobalWf G (.openm x T)
| defn :
  G&[] ⊢ T : .base b ->
  G&[],[] ⊢ t : T ->
  lookup x G = none ->
  GlobalWf G (.defn x T t)
| inst :
  lookup x G = some (.openm x T) ->
  G&[],[] ⊢ t : T ->
  GlobalWf G (.inst x t)
| instty :
  none = lookup x G ->
  ValidInstTy G x [] T ->
  GlobalWf G (.instty x T)

inductive ListGlobalWf : List Global -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G

inductive TypeMatch : Ty -> Ty -> Prop
| refl :
  TypeMatch R R
| arrow :
  TypeMatch B R ->
  TypeMatch (A -:> B) R
| all A :
  TypeMatch B[su A::+0] R ->
  TypeMatch (∀[K] B) R

inductive SpineType (G : List Global) (Δ : List Kind) (Γ : List Ty) : List SpineElem -> Ty -> Ty -> Prop where
| refl :
  -- G&Δ,Γ ⊢ t : T ->
  SpineType G Δ Γ [] T T
| term :
  G&Δ ⊢ A : ★ ->
  G&Δ,Γ ⊢ a : A ->
  G&Δ ⊢ (A -:> B) : ★ ->
  SpineType G Δ Γ sp (A -:> B) T ->
  SpineType G Δ Γ (sp ++ [.term a]) B T
| oterm :
  G&Δ ⊢ A : ◯ ->
  G&Δ,Γ ⊢ a : A ->
  SpineType G Δ Γ sp (A -:> B) T ->
  SpineType G Δ Γ (sp ++ [.oterm a]) B T
| type :
  G&Δ ⊢ a : K ->
  G&Δ ⊢ ∀[K]P : ★ ->
  P' = P[su a::+0] ->
  SpineType G Δ Γ sp (∀[K]P) T ->
  SpineType G Δ Γ (sp ++ [.type a]) P' T
