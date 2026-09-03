import LeanSubst
import Common.Vec

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
| classDecl {na : Nat} {Ks1 : Vec Core.Kind na} {mτs : List (String × _)}:
  lookup s G = none ->
  (∀ i j: Nat, (hi : i < mτs.length) -> (hj : j < mτs.length) -> i ≠ j -> (mτs[i]'hi).1 ≠ (mτs[j]'hj).1) ->
  (∀ (i : Nat) mn R, (hi : i < mτs.length) -> mτs[i]'hi = (mn, ⟨0, #(), 0, #(), 0, #(), R⟩) ∧
    mn ≠ s ∧ lookup mn G = none ∧ G&Ks1.list.reverse ⊢s R : ★) ->
  GlobalWf G (.classDecl s Ks1 /-fds scs-/ mτs)
| inst {na nb nc} {Ks1 Ks2 As} {ts : List (String × _)}:
  lookup x G = none ->
  spTy = ⟨na, Ks1, nb, Ks2, nc, As, R⟩ ->
  R.spine = some (cls, Tys) ->
  Δ = (Ks1 ++ Ks2).list.reverse ->
  (∀ i : Fin nc, G&Δ ⊢s As[i] : ★) ->
  G&Δ ⊢s R : ★ ->
  lookup cls G = some (.odata cls K mτs) ->
  -- Cover all methods
  mτs.length = ts.length ->
  (∀ i : Nat, (hi : i < mτs.length) ->
    ∃ j, ∃ (hj : j < ts.length), (mτs[i].1 = (ts[j]'hj).1)) ->

  GlobalWf G (.instDecl x spTy ts)

inductive ListGlobalWf : GlobalEnv -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G



end Surface
