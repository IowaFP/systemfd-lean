import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open Lilac
open LeanSubst

namespace Core

abbrev KindEnv := List Kind
abbrev TyEnv := List Ty

inductive VecTyping (J : A -> B -> Prop) : Vec A m -> Vec B m -> Prop
| nil : VecTyping J .nil .nil
| cons :
  J a b ->
  VecTyping J as bs ->
  VecTyping J (a::as) (b::bs)

def Ty.HeadVariable (A : Ty) (test : String -> Bool) : Prop :=
  ∃ x sp, A.spine = some (x, sp) ∧ test x

inductive Kinding (G : List Global) : List Kind -> Ty -> Kind -> Prop
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

notation:170 G:170 "&" Δ:170 " ⊢ " A:170 " : " K:170 => Kinding G Δ A K

def Ty.data? (c : DataConst) (G : List Global) (A : Ty) : Bool :=
  match A.spine with
  | some (x, _) => is_data c G x
  | none => false

def Ty.is_data (data1 : String) (A : Ty) : Bool :=
  match A.spine with
  | some (data2, _) => data1 == data2
  | none => false

inductive SpineKinding (sv : SpCtorVariant) (x : String) (G : List Global) (test : Ty -> Bool) : SpineTy -> Prop where
| valid {Ks1 : Vec Kind m1} {Ks2 : Vec Kind m2} {Ts : Vec _ n} :
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  (∀ (i : Fin n), G&Δ ⊢ Ts[i] : ★) ->
  G&Δ ⊢ R : ★ ->
  test R ->
  (sv = .openm -> ∀ (i : Fin n), Ts[i].data? .opn G) ->
  SpineKinding sv x G test ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩

-- inductive KindingPreamble (G : List Global) (Δ : List Kind) : List Ty -> Ty -> Ty -> Prop
-- | done : KindingPreamble G Δ [] T T
-- | cons {Ty : List Ty} :
--   G&Δ ⊢ A : K ->
--   KindingPreamble G Δ Ty T1[su A::+0] T2 ->
--   KindingPreamble G Δ (A::Ty) (∀[K] T1) T2

inductive PatternBinders (G : List Global) (Δ : List Kind) : (m : Nat) -> Vec Ty m -> Pattern m -> List Kind -> List Ty -> Prop
| zero : PatternBinders G Δ 0 ss ps [] []
| succ {Ts' : Vec _ nc} :
  lookup_spine_type G c = some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩ ->
  (∀ (i : Fin na), G&Δ ⊢ As[i] : Ks1[i]) ->
  Ts' = Ts[As.list.reverse.map su ++ Subst.id Ty]⟨.add Ty ℓ1.length⟩ ->
  R' = R[As.list.reverse.map su ++ Subst.id Ty] ->
  PatternBinders G Δ n S p ℓ1 ℓ2 ->
  PatternBinders G Δ (n + 1) (R'::S) (⟨c, na, As, nb, nc⟩::p) (ℓ1 ++ Ks2.list.reverse) (ℓ2 ++ Ts'.list.reverse)

/-
  data Term
  | nat : ∀ α, α ~ Nat -> Term α
  | app : ∀ α, Term α -> Term α -> Term α

-/

inductive CoercionProject (G : List Global) (Δ : List Kind) : Nat -> Ty -> Ty -> Prop where
| fst_app :
  G&Δ ⊢ A : (K1 -:> K2) ->
  CoercionProject G Δ 0 ((A • C) ~[K2]~ (B • D)) (A ~[K1 -:> K2]~ B)
| snd_app :
  G&Δ ⊢ C : K1 ->
  CoercionProject G Δ 1 ((A • C) ~[K2]~ (B • D)) (C ~[K1]~ D)
| fst_arrow :
  G&Δ ⊢ A : ★ ->
  CoercionProject G Δ 0 (A -:> C ~[★]~ B -:> D) (A ~[★]~ B)
| snd_arrow :
  G&Δ ⊢ C : ★ ->
  CoercionProject G Δ 1 (A -:> C ~[★]~ B -:> D) (C ~[★]~ D)

def Query (G : List Global) (c : DataConst) (qs : Vec String m) (Ts : Vec Ty m) : Prop :=
  VecTyping (lookup_ctor? G c · ·) qs Ts

def Query.Match (qs : Vec String m) (ps : Pattern m) : Prop :=
  VecTyping (λ q p => ∃ na As nb, p = ⟨q, na, As, nb⟩) qs ps

def OpenExhaustive (G : List Global) : Prop :=
  ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q},
  lookup x G = some (.openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  Query G .opn q Ts ->
  ∃ (i : Nat), ∃ b p, G[i]? = some (.inst x p b) ∧ Query.Match q p

inductive Typing (G : List Global) : List Kind -> List Ty -> Term -> Ty -> Prop
| var :
  Γ[x]? = some A ->
  G&Δ ⊢ A : ★ ->
  Typing G Δ Γ #x A
| defn :
  lookup_defn G x = some ⟨A, t⟩ ->
  G&Δ ⊢ A : ★ ->
  Typing G Δ Γ d#x A
----------------------------------------------------------------------------------------------------
---- Data
----------------------------------------------------------------------------------------------------
| spctor {Δ Γ m1 m2 n x v Ks1 Ks2 Ts Ts' R R'} {As : Vec Ty m1} {Bs : Vec Ty m2} {ts : Fun.Vec Term n} :
  lookup_spine_type G x = some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ ->
  Ts' = Ts[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  R' = R[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  (∀ (i : Fin m1), G&Δ ⊢ As[i] : Ks1[i]) ->
  (∀ (i : Fin m2), G&Δ ⊢ Bs[i] : Ks2[i]) ->
  (∀ (i : Fin n), Typing G Δ Γ (ts i) Ts'[i]) ->
  (∀ c, v = .data c -> lookup_ctor? G c x R) ->
  (v = .openm -> ∀ (i : Fin n), Ts[i].data? .opn G) ->
  Typing G Δ Γ (.spctor v x As Bs ts) R'
| mtch {ss S : Fun.Vec _ m} {ps ts ζ ξ : Fun.Vec _ n} :
  (∀ i, Typing G Δ Γ (ss i) (S i)) ->
  (∀ i, (S i).data? .cls G) ->
  (∀ i, PatternBinders G Δ m S (ps i) (ζ i) (ξ i)) ->
  (∀ i, Typing G (ζ i ++ Δ) (ξ i ++ Γ)⟨.add Ty (ζ i).length⟩ (ts i) T⟨.add Ty (ζ i).length⟩) ->
  (∀ {q}, Query G .cls q S -> ∃ i, Query.Match q (ps i)) ->
  Typing G Δ Γ (.mtch m n ss ps ts) T
----------------------------------------------------------------------------------------------------
---- Terms
----------------------------------------------------------------------------------------------------
| lam {Γ : List Ty} :
  G&Δ ⊢ A : ★ ->
  Typing G Δ (A::Γ) t B ->
  Typing G Δ Γ (λ[A] t) (A -:> B)
| app :
  Typing G Δ Γ f (A -:> B) ->
  Typing G Δ Γ a A ->
  Typing G Δ Γ (f • a) B
| lamt :
  Kinding G Δ (∀[K]P) ★ ->
  Typing G (K::Δ) Γ⟨.succ Ty⟩ t P ->
  Typing G Δ Γ (Λ[K] t) (∀[K] P)
| appt :
  Typing G Δ Γ f (∀[K] P) ->
  G&Δ ⊢ a : K ->
  P' = P[su a::+0σ] ->
  Typing G Δ Γ (f •[a]) P'
----------------------------------------------------------------------------------------------------
---- Coercions
----------------------------------------------------------------------------------------------------
| refl :
  G&Δ ⊢ A : K ->
  Typing G Δ Γ (refl! A) (A ~[K]~ A)
| cast :
  G&(K::Δ) ⊢ R : ★ ->
  Typing G Δ Γ c (A ~[K]~ B) ->
  Typing G Δ Γ t R[su A::+0σ] ->
  R' = R[su B::+0σ] ->
  Typing G Δ Γ (.cast R c t) R'
| prj :
  Typing G Δ Γ c T ->
  CoercionProject G Δ n T R ->
  Typing G Δ Γ (prj[n] c) R
| allc :
  Typing G (K::Δ) Γ⟨.succ Ty⟩ t (A ~[★]~ B) ->
  Typing G Δ Γ (∀c[K] t) ((∀[K] A) ~[★]~ (∀[K] B))
| apptc :
  Typing G Δ Γ f ((∀[K] A) ~[★]~ (∀[K] B)) ->
  Typing G Δ Γ a (C ~[K]~ D) ->
  A' = A[su C::+0σ] ->
  B' = B[su D::+0σ] ->
  Typing G Δ Γ (f •c[a]) (A' ~[★]~ B')

notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢ " t:170 " : " A:170 => Typing G Δ Γ t A

-- inductive ValidCtor (x : String) : Ty -> Prop where
-- | base :
--   T.spine = some (x, sp) ->
--   ValidCtor x T
-- | all :
--   ValidCtor x P ->
--   ValidCtor x (∀[K] P)
-- | arrow :
--   ValidCtor x B ->
--   ValidCtor x (A -:> B)

-- inductive ValidOpenKind : Kind -> Prop where
-- | base : ValidOpenKind ★
-- | arrow : ValidOpenKind B -> ValidOpenKind (A -:> B)

-- inductive ValidInstTy (G : List Global) (x : String) : List Kind -> Ty -> Prop where
-- | base :
--   T.spine = some (x, sp) ->
--   G&Δ ⊢ T : ★ ->
--   ValidInstTy G x Δ T
-- | all :
--   G& (K::Δ) ⊢ T : ★ ->
--   ValidInstTy G x (K::Δ) T ->
--   ValidInstTy G x Δ (∀[K] T)
-- | arrow :
--   ValidInstTy G x Δ T ->
--   G&Δ ⊢ A : ★ ->
--   ValidInstTy G x Δ (A -:> T)

-- (m : Nat) × Vec Kind m × (n : Nat) × Vec Ty n × Ty

inductive PatternPartTyping G Δ : String × (n : Nat) × Vec Ty n × Nat × Nat -> Ty -> Prop
| valid :
  lookup_spine_type G c = some ⟨na, Ks, nb1, Bs1, nb2, Bs2, R⟩ ->
  -- Sequ.append_vec (Vec.map su As) +0 = τ ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks[i]) ->
  R' = R[As.list.reverse.map su ++ Subst.id Ty] ->
  PatternPartTyping G Δ ⟨c, na, As, nb1, nb2⟩ R'

def PatternTyping (G : List Global) (Δ : List Kind) (ps : Pattern m) (Ts : Vec Ty m) : Prop :=
  VecTyping (PatternPartTyping G Δ) ps Ts

-- inductive ConstructorTyping G Δ Γ : Constructor -> Ty -> Prop
-- | valid {ts : Vec Term nt} :
--   lookup_spine_type G c = some ⟨na, Ks, nt1, Ts1, nt2, Ts2, R⟩ ->
--   (∀ i : Fin na, G&Δ ⊢ As[i] : Ks[i]) ->
--   (∀ i : Fin nt, G&Δ,Γ ⊢ ts[i] : Ts[i][As.list.reverse.map su ++ Subst.id Ty]) ->
--   R' = R[τ] ->
--   ConstructorTyping G Δ Γ ⟨c, na, As, nt, ts⟩ R'

-- def VecConstructorTyping (G : List Global) (Δ : List Kind) (Γ : List Ty) (cs : Vec Constructor n) (Ts : Vec Ty n) : Prop :=
--   VecTyping (ConstructorTyping G Δ Γ) cs Ts

inductive GlobalWf : List Global -> Global -> Prop where
| data {G : GlobalEnv} {ctors : Vec (String × SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    SpineKinding (.data .cls) y (.data 0 x K #()::G) (Ty.is_data x) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data n x K ctors)
| odata :
  lookup x G = none ->
  GlobalWf G (.odata x K)
| openm :
  SpineKinding .openm x G (λ _ => true) T ->
  lookup x G = none ->
  GlobalWf G (.openm x T)
| defn :
  G&[] ⊢ T : ★ ->
  G&[],[] ⊢ t : T ->
  lookup x G = none ->
  GlobalWf G (.defn x T t)
| inst :
  lookup x G = some (.openm x ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  PatternBinders G Δ n Ts p ζ Γ ->
  G&(ζ ++ Δ),Γ⟨.add Ty ζ.length⟩ ⊢ t : R⟨.add Ty ζ.length⟩ ->
  GlobalWf G (.inst x p t)
| octor :
  SpineKinding (.data .opn) x G (Ty.data? .opn G) T ->
  lookup x G = none ->
  GlobalWf G (.octor x T)

inductive ListGlobalWf : List Global -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G

inductive EntryWf : List Global -> Entry -> Prop where
| data :
  lookup x G = some (.data x K ctors) ->
  EntryWf G (.data x K ctors)
| ctor z K (ctors : Vec _ n) (i : Fin n) :
  lookup z G = some (.data z K ctors) ->
  ctors[i] = (x, T) ->
  SpineKinding (.data .cls) x G (Ty.is_data z) T ->
  lookup x G = some (.ctor x i T) ->
  EntryWf G (.ctor x i T)
| odata :
  lookup x G = some (.odata x K) ->
  EntryWf G (.odata x K)
| openm :
  SpineKinding .openm x G (λ _ => true) T ->
  lookup x G = some (.openm x T) ->
  EntryWf G (.openm x T)
| defn :
  G&[] ⊢ T : ★ ->
  G&[],[] ⊢ t : T ->
  lookup x G = some (.defn x T t) ->
  EntryWf G (.defn x T t)
| octor :
  SpineKinding (.data .opn) x G (Ty.data? .opn G) T ->
  lookup x G = some (.octor x T) ->
  EntryWf G (.octor x T)

-- inductive TypeMatch : Ty -> Ty -> Prop
-- | refl :
--   TypeMatch R R
-- | arrow :
--   TypeMatch B R ->
--   TypeMatch (A -:> B) R
-- | all A :
--   TypeMatch B[su A::+0] R ->
--   TypeMatch (∀[K] B) R

-- inductive SpineType (G : List Global) (Δ : List Kind) (Γ : List Ty) : List SpineElem -> Ty -> Ty -> Prop where
-- | refl :
--   -- G&Δ,Γ ⊢ t : T ->
--   SpineType G Δ Γ [] T T
-- | term :
--   G&Δ ⊢ A : ★ ->
--   G&Δ,Γ ⊢ a : A ->
--   G&Δ ⊢ (A -:> B) : ★ ->
--   SpineType G Δ Γ sp (A -:> B) T ->
--   SpineType G Δ Γ (sp ++ [.term a]) B T
-- | oterm :
--   G&Δ ⊢ A : ◯ ->
--   G&Δ,Γ ⊢ a : A ->
--   SpineType G Δ Γ sp (A -:> B) T ->
--   SpineType G Δ Γ (sp ++ [.oterm a]) B T
-- | type :
--   G&Δ ⊢ a : K ->
--   G&Δ ⊢ ∀[K]P : ★ ->
--   P' = P[su a::+0] ->
--   SpineType G Δ Γ sp (∀[K]P) T ->
--   SpineType G Δ Γ (sp ++ [.type a]) P' T

end Core
