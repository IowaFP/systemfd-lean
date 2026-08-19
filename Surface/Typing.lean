import LeanSubst
import Core.Vec

-- import Surface.Ty
import Surface.Term
import Surface.Global

open Lilac
namespace Surface

@[simp]
abbrev KindEnv := List Core.Kind

@[simp]
abbrev TyEnv := List Core.Ty


inductive Kinding (G : GlobalEnv) : KindEnv -> Core.Ty -> Core.Kind -> Prop
| var :
  Δ[x]? = some K ->
  Kinding G Δ t#x K
| global :
  lookup_kind G x = some K ->
  Kinding G Δ gt#x K
| arrow :
  Kinding G Δ A ★ ->
  Kinding G Δ B ★ ->
  Kinding G Δ (A -:> B) ★
| all :
  Kinding G (K::Δ) P ★ ->
  Kinding G Δ (∀[K] P) ★
| app :
  Kinding G Δ f (A -:> B) ->
  Kinding G Δ a A ->
  Kinding G Δ (f • a) B


notation:170 G:170 "&" Δ:170 " ⊢s " A:170 " : " K:170 => Kinding G Δ A K

inductive ValidCtor (x : String) : Core.Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidCtor x T
| all :
  ValidCtor x P ->
  ValidCtor x (∀[K] P)
| arrow :
  ValidCtor x B ->
  ValidCtor x (A -:> B)

-- Valid Class Methods are of the form
-- ∀αs (x βs) => B
-- inductive ValidClassMethodTy (x : String) : Core.Ty -> Prop where
-- | base :
--   T.spine = some (x, sp) ->
--   ValidClassMethodTy x T
-- | all :
--   ValidClassMethodTy x P ->
--   ValidClassMethodTy x (∀[K] P)
-- | arrow :
--   A.spine = some (x, sp) ->
--   ValidClassMethodTy x (A `=:> B)

-- inductive ValidOpenKind : Kind -> Prop where
-- | base : ValidOpenKind `◯
-- | arrow : ValidOpenKind B -> ValidOpenKind (A `-:> B)


inductive ValidClassInstTy (x : String) : Core.Ty -> Prop where
| base :
  T.spine = some (x, sp) ->
  ValidClassInstTy x T

inductive GlobalWf : GlobalEnv -> Surface.Global -> Prop where
| data {n : Nat} {G : GlobalEnv} {ctors : Vec (String × Core.SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data (n := n) x K ctors)
| defn :
  lookup x G = none ->
  GlobalWf G (.defn x T t)
| classDecl {mτs : List (String × _)}:
  lookup s G = none ->
  ∀ i j: Nat, (hi : i < mτs.length) -> (hj : j < mτs.length) -> i ≠ j -> (mτs[i]'hi).1 ≠ (mτs[j]'hj).1 ->
  (∀ i : Nat, (hi : i < mτs.length) -> mτs[i]'hi = (mn, T) ->
    mn ≠ s ∧ lookup mn G = none) ->
  GlobalWf G (.classDecl s Ks fds scs mτs)
| inst {ts : List (String × _)}:
  lookup x G = some (.odata x K mτs) ->
  -- TODO : ts cover all methods
  mτs.length = ts.length ->
  (∀ i : Nat, (hi : i < ts.length) -> (ts[i]'hi).1 = mn ->
    ∃ j, (hj : j < mτs.length) ->  mτs[j].1 = mn) ->
  -- lookup x G = some (.openm x ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  -- (Ks1.list ++ Ks2.list).reverse = Δ ->
  -- PatternBinders .opn G Δ n Ts p ζ Γ ->
  -- G&(ζ ++ Δ),Γ ⊢ t : R⟨.add Ty ζ.length⟩ ->
  GlobalWf G (.instDecl x spTy ts)

inductive ListGlobalWf : GlobalEnv -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G



end Surface
