import LeanSubst
import Core.Vec

import Surface.Ty
import Surface.Term
import Surface.Global

namespace Surface

def KindEnv := List Kind
def TyEnv := List Ty


instance inst_getElem_TyEnv : GetElem TyEnv Nat Ty (λ env i => by simp [TyEnv] at env; apply i < env.length) where
  getElem env i _ := by unfold TyEnv at env; apply env[i]

instance inst_getElem?_TyEnv : GetElem? TyEnv Nat Ty
         (λ env i => by simp [TyEnv] at env; apply i < env.length) where
  getElem? env i := by unfold TyEnv at env; apply env[i]?

instance inst_getElem_KindEnv : GetElem KindEnv Nat Kind
         (λ env i => by simp [KindEnv] at env; apply i < env.length) where
  getElem env i _ := by unfold KindEnv at env; apply env[i]

instance inst_getElem?_KindEnv : GetElem? KindEnv Nat Kind
         (λ env i => by simp [KindEnv] at env; apply i < env.length) where
  getElem? env i := by unfold KindEnv at env; apply env[i]?

def TyEnv.mapM [Monad m] (f : Ty -> m β) (env : TyEnv) := by simp [TyEnv] at env; apply env.mapM f

def KindEnv.map (f : Kind -> β) (env : KindEnv) := by simp [KindEnv] at env; apply env.map f


def ValidHeadVariable (t : Term) (test : String -> Bool) : Prop :=
  ∃ x, Term.spine t = some x ∧ test x.fst

def ValidTyHeadVariable (t : Ty) (test : String -> Bool) : Prop :=
  ∃ x, Ty.spine t = some x ∧ test x.fst

inductive StableTypeMatch : KindEnv -> Ty -> Ty -> Prop
| refl :
  Ty.spine R = some x ->
  StableTypeMatch Δ R R
| arrow :
  StableTypeMatch Δ B R ->
  StableTypeMatch Δ (A `-:> B) R
| all :
  StableTypeMatch (K::Δ) B R[+1] ->
  StableTypeMatch Δ (`∀[K] B) R


inductive PrefixTypeMatch : KindEnv -> Ty -> Ty -> Ty -> Prop
| refl :
  Ty.spine B = some x ->
  PrefixTypeMatch Δ B T T
| arrow :
  PrefixTypeMatch Δ B V T ->
  PrefixTypeMatch Δ (A `-:> B) (A `-:> V) T
| all :
  PrefixTypeMatch (K::Δ) B V T[+1] ->
  PrefixTypeMatch Δ (`∀[K] B) (`∀[K] V) T


inductive Kinding (G : GlobalEnv) : KindEnv -> Ty -> Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t`#x K
| global :
  lookup_kind G x = some K ->
  Kinding G Δ gt`#x K
| arrow :
  Kinding G Δ A (.base b1) ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A `-:> B) `★
| all :
  Kinding G (K::Δ) P `★ ->
  Kinding G Δ (`∀[K] P) `★
| app :
  Kinding G Δ f (A `-:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f `• a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Kinding G Δ A K

inductive Typing (G : GlobalEnv) :
  KindEnv -> TyEnv -> Term -> Ty -> Prop
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
  P' = P[.su a :: +0:Ty] ->
  Typing G Δ Γ (f `•[a]) P'

notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " : " A:170 => Typing G Δ Γ t A

inductive ValidCtor (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidCtor x T
| all :
  ValidCtor x P ->
  ValidCtor x (`∀[K] P)
| arrow :
  ValidCtor x B ->
  ValidCtor x (A `-:> B)


inductive GlobalWf : GlobalEnv -> Global -> Prop where
| data {ctors : Vec (String × Ty) n} {ctors' : Vec String n} {G : GlobalEnv}:
  (∀ i y T, ctors i = (y, T) ->
    (.data x K v[]::G)&[] ⊢s T : `★ ∧
     ValidCtor x T ∧
     none = lookup y (.data x K v[]::G)) ->
  (ctors' = λ i => (ctors i).1) ->
   ctors'.HasUniqueElems ->
  lookup x G = none ->
  GlobalWf G (.data x K ctors)

inductive ListGlobalWf : GlobalEnv -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)


notation:175 "⊢s " G:175 => ListGlobalWf G

end Surface
