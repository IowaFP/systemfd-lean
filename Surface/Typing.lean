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
| eq :
  Kinding G Δ A K ->
  Kinding G Δ B K ->
  Kinding G Δ (A ~[K]~ B) ★


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

def Ty.data? (c : Core.DataConst) (G : List Global) (A : Core.Ty) : Bool :=
  match A.spine with
  | some (x, _) => is_data c G x
  | none => false

inductive SpineKinding (sv : Core.SpCtorVariant) (x : String) (G : GlobalEnv) (test : Core.Ty -> Bool) : Core.SpineTy -> Prop where
| valid {Ks1 : Vec Core.Kind m1} {Ks2 : Vec Core.Kind m2} {Ts : Vec _ n} :
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  (∀ (i : Fin n), G&Δ ⊢s Ts[i] : ★) ->
  G&Δ ⊢s R : ★ ->
  test R ->
  (sv = .openm -> ∀ (i : Fin n), Surface.Ty.data? .opn G Ts[i]) ->
  SpineKinding sv x G test ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩


inductive GlobalWf : GlobalEnv -> Surface.Global -> Prop where
| data {n : Nat} {G : GlobalEnv} {ctors : Vec (String × Core.SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    SpineKinding (.data .cls) y ((.data x K #())::G) (Core.Ty.is_data x) T ∧
    x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data (n := n) x K ctors)
| defn :
  lookup x G = none ->
  G&[] ⊢s T : ★ ->
  GlobalWf G (.defn x T t)
| classDecl {na : Nat} {Ks1 : Vec Core.Kind na} {mτs : List (String × Core.SpineTy)}:
  lookup s G = none ->
  (∀ i j: Nat, (hi : i < mτs.length) -> (hj : j < mτs.length) -> i ≠ j -> (mτs[i]'hi).1 ≠ (mτs[j]'hj).1) ->
  (∀ (i : Nat) mn τ, (hi : i < mτs.length) -> mτs[i] = (mn, τ) ->
    SpineKinding Core.SpCtorVariant.openm mn (.classDecl s Ks1 [] :: G) (λ _ => true) τ) ->
  (∀ (i : Nat) mn R, (hi : i < mτs.length) -> mτs[i]'hi = (mn, ⟨0, #(), 0, #(), 0, #(), R⟩) ∧
    mn ≠ s ∧ lookup mn G = none ∧ G&Ks1.list.reverse ⊢s R : ★) ->
  GlobalWf G (.classDecl s Ks1 /-fds scs-/ mτs)
| inst {na nb nc} {Ks1 Ks2 As} {ts : List (String × _)}:
  lookup x G = none ->
  lookup cls_name G = some (.odata cls_name K mτs) ->
  SpineKinding (.data .opn) x G (Ty.data? .opn G) ⟨na, Ks1, nb, Ks2, nc, As, (gt#cls_name).mkApps_nats (List.range na).reverse⟩ ->
  -- Cover all methods
  (e : mτs.length = ts.length) ->
  (∀ i : Nat, (hi : i < ts.length) ->
    (mτs[i].1 = (ts[i]).1)) ->

  GlobalWf G (.instDecl x ⟨na, Ks1, nb, Ks2, nc, As, (gt#cls_name).mkApps_nats (List.range k1).reverse⟩ ts)

inductive ListGlobalWf : GlobalEnv -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G


theorem GlobalWf.drop_lookup_unique {G : List Global} n :
  ⊢ G ->
  lookup x (G.drop n) = some t ->
  lookup x G = some t
:= by
  intro wf j
  induction wf generalizing n <;> try simp at *
  case nil => exact j
  case cons G j1 j2 wf ih =>
    cases n <;> simp at *
    case zero => exact j
    case succ n =>
      replace ih := ih n j
      cases j2
      case data n y K ctors j1 j2 j3 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j3; injection j3
        case _ e =>
          simp [Vec.foldr_or_val_some]
          apply Or.inr; apply And.intro;
          apply ih; grind
      case classDecl T b y j1 j2 =>
        sorry
        -- simp [lookup]; split
        -- case _ e => subst e; rw [ih] at j2; injection j2
        -- case _ e => exact ih
      case defn T b t' y j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j1; simp at j1
        case _ e => exact ih
      case inst y T t' j1 j2 => simp [lookup]; sorry; -- exact ih


theorem lookup_weaken (wf : ⊢ (g::G)) : lookup x G = some e -> lookup x (g::G) = some e := by
  intro h; apply GlobalWf.drop_lookup_unique 1 wf h

theorem lookup_kind_weaken (wf : ⊢ (g::G))
  : lookup_kind G x = some K -> lookup_kind (g::G) x = some K
:= by
  intro h; simp_all [lookup_kind, Option.map]
  generalize zdef : lookup x G = z at *
  generalize wdef : lookup x (g::G) = w at *
  cases z; simp at h; case _ z =>
  cases w
  case _ =>
    simp_all
    replace zdef := lookup_weaken wf zdef
    rw [wdef] at zdef; cases zdef
  case _ w =>
    simp_all
    have lem := lookup_weaken wf zdef
    rw [wdef] at lem; cases lem; exact h



theorem Kinding.weaken_global (wf : ⊢ (g::G)) : G&Δ ⊢s A : K -> (g::G)&Δ ⊢s A : K
| var h => var h
| global h => global $ lookup_kind_weaken wf h
| arrow j1 j2 => arrow (j1.weaken_global wf) (j2.weaken_global wf)
| all j1 => all (j1.weaken_global wf)
| app j1 j2 => app (j1.weaken_global wf) (j2.weaken_global wf)
| eq j1 j2 => eq (j1.weaken_global wf) (j2.weaken_global wf)



end Surface
