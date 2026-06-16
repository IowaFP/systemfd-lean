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

abbrev Ty.data? (c : DataConst) (G : List Global) (A : Ty) : Prop := A.HeadVariable (is_data c G)

inductive SpineKinding (sv : SpCtorVariant) (x : String) (G : List Global) : SpineTy -> Prop where
| valid {Ks : Vec Kind m} {Ts : Vec _ n} :
  Vec.to_list Ks = Δ ->
  (∀ (i : Fin n), G&Δ ⊢ Ts[i] : ★) ->
  G&Δ ⊢ R : ★ ->
  (∀ c, sv = .data c -> lookup_ctor? G c x R) ->
  (sv = .openm -> ∀ (i : Fin n), Ts[i].data? .opn G) ->
  SpineKinding sv x G ⟨m, Ks, n, Ts, R⟩

inductive PatternBinders (G : List Global) (Δ : List Kind) : (m : Nat) -> Vec Ty m -> Pattern m -> List Ty -> Prop
| zero : PatternBinders G Δ 0 ss ps []
| succ {Ts' : Vec _ nb} :
  lookup_spine_type G c = some ⟨na, Ks, nb, Ts, R⟩ ->
  (∀ (i : Fin na), G&Δ ⊢ As[i] : Ks[i]) ->
  Ts' = Ts[Sequ.append_vec (Vec.map su As) +0:Ty] ->
  R' = R[Sequ.append_vec (Vec.map su As) +0:Ty] ->
  PatternBinders G Δ n S p ℓ ->
  PatternBinders G Δ (n + 1) (R'::S) (⟨c, na, As, nb⟩::p) ((Vec.to_list Ts') ++ ℓ)

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
  ∀ {x na nb} {τ : Subst Ty} {As Ks : Vec _ na} {Ts Ts' : Vec _ nb} {Δ R q},
  lookup x G = some (.openm x ⟨na, Ks, nb, Ts, R⟩) ->
  (∀ (i : Fin na), G&Δ ⊢ As[i] : Ks[i]) ->
  Sequ.append_vec (Vec.map su As) +0 = τ ->
  Vec.map (·[τ]) Ts = Ts' ->
  Query G .opn q Ts' ->
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

| spctor {Δ Γ m n x v Ks Ts Ts' R R'} {As : Vec Ty m} {ts : Fun.Vec Term n} :
  lookup_spine_type G x = some ⟨m, Ks, n, Ts, R⟩ ->
  Ts' = Ts[Sequ.append_vec (Vec.map su As) +0:Ty] ->
  R' = R[Sequ.append_vec (Vec.map su As) +0:Ty] ->
  (∀ (i : Fin m), G&Δ ⊢ As[i] : Ks[i]) ->
  (∀ (i : Fin n), Typing G Δ Γ (ts i) Ts'[i]) ->
  (∀ c, v = .data c -> lookup_ctor? G c x R) ->
  (v = .openm -> ∀ (i : Fin n), Ts'[i].data? .opn G) ->
  Typing G Δ Γ (.spctor v x As ts) R'

| mtch {ss S : Fun.Vec _ m} {ps ts ξ : Fun.Vec _ n} :
  (∀ i, Typing G Δ Γ (ss i) (S i)) ->
  (∀ i, (S i).data? .cls G) ->
  (∀ i, PatternBinders G Δ m S (ps i) (ξ i)) ->
  (∀ i, Typing G Δ (ξ i ++ Γ) (ts i) T) ->
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
  Typing G (K::Δ) Γ[+1:Ty] t P ->
  Typing G Δ Γ (Λ[K] t) (∀[K] P)
| appt :
  Typing G Δ Γ f (∀[K] P) ->
  G&Δ ⊢ a : K ->
  P' = P[su a::+0] ->
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
  Typing G Δ Γ t R[su A::+0] ->
  R' = R[su B::+0] ->
  Typing G Δ Γ (.cast R c t) R'
| prj :
  Typing G Δ Γ c T ->
  CoercionProject G Δ n T R ->
  Typing G Δ Γ (prj[n] c) R
| allc :
  Typing G (K::Δ) Γ[+1:Ty] t (A ~[★]~ B) ->
  Typing G Δ Γ (∀c[K] t) ((∀[K] A) ~[★]~ (∀[K] B))
| apptc :
  Typing G Δ Γ f ((∀[K] A) ~[★]~ (∀[K] B)) ->
  Typing G Δ Γ a (C ~[K]~ D) ->
  A' = A[su C::+0] ->
  B' = B[su D::+0] ->
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

inductive PatternPartTyping G Δ : String × (n : Nat) × Vec Ty n × Nat -> Ty -> Prop
| valid :
  lookup_spine_type G c = some ⟨na, Ks, nb, Bs, R⟩ ->
  Sequ.append_vec (Vec.map su As) +0 = τ ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks[i]) ->
  R' = R[τ] ->
  PatternPartTyping G Δ ⟨c, na, As, nb⟩ R'

def PatternTyping (G : List Global) (Δ : List Kind) (ps : Pattern m) (Ts : Vec Ty m) : Prop :=
  VecTyping (PatternPartTyping G Δ) ps Ts

inductive ConstructorTyping G Δ Γ : Constructor -> Ty -> Prop
| valid {ts : Vec Term nt} :
  lookup_spine_type G c = some ⟨na, Ks, nt, Ts, R⟩ ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks[i]) ->
  Sequ.append_vec (Vec.map su As) +0 = τ ->
  (∀ i : Fin nt, G&Δ,Γ ⊢ ts[i] : Ts[i][τ]) ->
  R' = R[τ] ->
  ConstructorTyping G Δ Γ ⟨c, na, As, nt, ts⟩ R'

def VecConstructorTyping (G : List Global) (Δ : List Kind) (Γ : List Ty) (cs : Vec Constructor n) (Ts : Vec Ty n) : Prop :=
  VecTyping (ConstructorTyping G Δ Γ) cs Ts

inductive GlobalWf : List Global -> Global -> Prop where
| data {G : GlobalEnv} {ctors : Vec (String × SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    SpineKinding (.data .cls) y (.data 0 x K .nil::G) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  lookup x G = none ->
  GlobalWf G (.data n x K ctors)
| odata :
  lookup x G = none ->
  GlobalWf G (.odata x K)
| openm :
  SpineKinding .openm x G T ->
  lookup x G = none ->
  GlobalWf G (.openm x T)
| defn :
  G&[] ⊢ T : ★ ->
  G&[],[] ⊢ t : T ->
  lookup x G = none ->
  GlobalWf G (.defn x T t)
| inst :
  lookup x G = some (.openm x ⟨m, Ks, n, Ts, R⟩) ->
  Vec.to_list Ks = Δ ->
  PatternBinders G Δ n Ts p Γ ->
  G&Δ,Γ ⊢ t : R ->
  GlobalWf G (.inst x p t)
| octor :
  SpineKinding (.data .opn) x G T ->
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
  SpineKinding (.data .cls) x G T ->
  lookup x G = some (.ctor x i T) ->
  EntryWf G (.ctor x i T)
| odata :
  lookup x G = some (.odata x K) ->
  EntryWf G (.odata x K)
| openm :
  SpineKinding .openm x G T ->
  lookup x G = some (.openm x T) ->
  EntryWf G (.openm x T)
| defn :
  G&[] ⊢ T : ★ ->
  G&[],[] ⊢ t : T ->
  lookup x G = some (.defn x T t) ->
  EntryWf G (.defn x T t)
| octor :
  SpineKinding (.data .opn) x G T ->
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
