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
def TyEnv.map (f : Ty -> β) (env : TyEnv) := by simp [TyEnv] at env; apply env.map f

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
  Kinding G Δ A `★ ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A `-:> B) `★
| «then» :
  Kinding G Δ A `◯ ->
  Kinding G Δ B (.base b2) ->
  Kinding G Δ (A `=:> B) `★
| all :
  Kinding G (K::Δ) P `★ ->
  Kinding G Δ (`∀[K] P) `★
| app :
  Kinding G Δ f (A `-:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f `• a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Kinding G Δ A K

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

-- Valid Class Methods are of the form
-- ∀αs (x βs) => B
inductive ValidClassMethodTy (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidClassMethodTy x T
| all :
  ValidClassMethodTy x P ->
  ValidClassMethodTy x (`∀[K] P)
| arrow :
  A.spine = some (x, sp) ->
  ValidClassMethodTy x (A `=:> B)

inductive ValidOpenKind : Kind -> Prop where
| base : ValidOpenKind `◯
| arrow : ValidOpenKind B -> ValidOpenKind (A `-:> B)


inductive ValidClassInstTy (x : String) : Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidClassInstTy x T

end Surface
