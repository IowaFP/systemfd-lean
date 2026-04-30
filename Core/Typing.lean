import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open Lilac
open LeanSubst

namespace Core

abbrev KindEnv := List Kind
abbrev TyEnv := List Ty


-- None of this should be needed...
-- instance inst_getElem_TyEnv : GetElem TyEnv Nat Ty (λ env i => by simp [TyEnv] at env; apply i < env.length) where
--   getElem env i _ := by unfold TyEnv at env; apply env[i]

-- instance inst_getElem?_TyEnv : GetElem? TyEnv Nat Ty
--          (λ env i => by simp [TyEnv] at env; apply i < env.length) where
--   getElem? env i := by unfold TyEnv at env; apply env[i]?

-- instance inst_getElem_KindEnv : GetElem KindEnv Nat Kind
--          (λ env i => by simp [KindEnv] at env; apply i < env.length) where
--   getElem env i _ := by unfold KindEnv at env; apply env[i]

-- instance inst_getElem?_KindEnv : GetElem? KindEnv Nat Kind
--          (λ env i => by simp [KindEnv] at env; apply i < env.length) where
--   getElem? env i := by unfold KindEnv at env; apply env[i]?

-- def TyEnv.mapM [Monad m] (f : Ty -> m β) (env : TyEnv) := by simp [TyEnv] at env; apply env.mapM f
-- def TyEnv.map (f : Ty -> β) (env : TyEnv) := by simp [TyEnv] at env; apply env.map f

-- def KindEnv.map (f : Kind -> β) (env : KindEnv) := by simp [KindEnv] at env; apply env.map f


-- def ValidHeadVariable (t : Term) (test : String -> Bool) : Prop :=
--   ∃ x, Term.spine t = some x ∧ test x.fst

def Ty.HeadVariable (A : Ty) (test : String -> Bool) : Prop :=
  ∃ x sp, A.spine = some (x, sp) ∧ test x

-- def ValidTyHeadVariable (t : Ty) (test : String -> Bool) : Prop :=
--   ∃ x, Ty.spine t = some x ∧ test x.fst

-- inductive StableTypeMatch : List Kind -> Ty -> Ty -> Prop
-- | refl :
--   Ty.spine R = some x ->
--   StableTypeMatch Δ R R
-- | arrow :
--   StableTypeMatch Δ B R ->
--   StableTypeMatch Δ (A -:> B) R
-- | all :
--   StableTypeMatch (K::Δ) B R[+1] ->
--   StableTypeMatch Δ (∀[K] B) R

-- inductive PrefixTypeMatch : List Kind -> Ty -> Ty -> Ty -> Prop
-- | refl :
--   Ty.spine B = some x ->
--   PrefixTypeMatch Δ B T T
-- | arrow :
--   PrefixTypeMatch Δ B V T ->
--   PrefixTypeMatch Δ (A -:> B) (A -:> V) T
-- | all :
--   PrefixTypeMatch (K::Δ) B V T[+1] ->
--   PrefixTypeMatch Δ (∀[K] B) (∀[K] V) T

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

inductive SpineKinding (G : List Global) : SpineTy -> Prop where
| valid {Ks : Vec Kind m} {Ts : Vec _ n} :
  Vec.to_list Ks = Δ ->
  (∀ (i : Fin n), G&Δ ⊢ Ts[i] : ★) ->
  G&Δ ⊢ R : ★ ->
  SpineKinding G ⟨m, Ks, n, Ts, R⟩

-- inductive KindingPreamble (G : List Global) (Δ : List Kind) : List Ty -> Ty -> Ty -> Prop
-- | done : KindingPreamble G Δ [] T T
-- | cons {Ty : List Ty} :
--   G&Δ ⊢ A : K ->
--   KindingPreamble G Δ Ty T1[su A::+0] T2 ->
--   KindingPreamble G Δ (A::Ty) (∀[K] T1) T2

inductive PatternBinders : (m : Nat) -> Vec Ty m -> Pattern m -> List Ty -> Prop
| zero : PatternBinders 0 ss ps []
| succ {Ts' : Vec _ nb} :
  lookup_spine_type G c = some ⟨na, Ks, nb, Ts, R⟩ ->
  (∀ (i : Fin na), G&Δ ⊢ As[i] : Ks[i]) ->
  Sequ.append_vec (Vec.map su As) +0 = τ ->
  (∀ (i : Fin nb), Ts'[i] = Ts[i][τ]) ->
  R' = R[τ] ->
  PatternBinders n S p ℓ ->
  PatternBinders (n + 1) (R'::S) (⟨c, na, As, nb⟩::p) ((Vec.to_list Ts') ++ ℓ)

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

-- def Ty.ctor? (G : List Global) (ctor : String) (A : Ty) : Prop :=
--   ∃ D sp, A.spine = some (D, sp) ∧ Global.ctor? G ctor D

abbrev Ty.data? (c : DataConst) (G : List Global) (A : Ty) : Prop := A.HeadVariable (is_data c G)

inductive Query (G : List Global) : Vec String m -> Vec Ty m -> Prop where
| nil : Query G .nil .nil
| cons :
  lookup_ctor? G q A ->
  Query G qs As ->
  Query G (q::qs) (A::As)

inductive Query.Match : Vec String m -> Pattern m -> Prop where
| nil : Query.Match .nil .nil
| cons :
  Query.Match qs ps ->
  Query.Match (q::qs) (⟨q, na, As, nb⟩::ps)

def OpenExhaustive (x : String) (G : List Global) : Prop :=
  ∀ {na nb} {Ks : Vec _ na} {Ts : Vec _ nb} {R q},
  lookup x G = some (.openm x ⟨na, Ks, nb, Ts, R⟩) ->
  Query G q Ts ->
  ∃ i b p, get_instance x i G = some ⟨nb, p, b⟩ ∧ Query.Match q p

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
---- Closed Data
----------------------------------------------------------------------------------------------------
| spctor {As : Vec Ty m} {ts : Fun.Vec Term n} :
  lookup_spine_type G x = some ⟨m, Ks, n, Ts, R⟩ ->
  (∀ (i : Fin m), G&Δ ⊢ As[i] : Ks[i]) ->
  Sequ.append_vec (Vec.map su As) +0 = τ ->
  (∀ (i : Fin n), Typing G Δ Γ (ts i) Ts[i][τ]) ->
  (∃ c, v = .data c -> lookup_ctor? G x R) ->
  (v = .openm -> ∀ (i : Fin n), Ts[i].data? .opn G) ->
  R' = R[τ] ->
  Typing G Δ Γ (.spctor v x As ts) R'
| mtch {ss S : Fun.Vec _ m} {ps ts ξ : Fun.Vec _ n} :
  (∀ i, Typing G Δ Γ (ss i) (S i)) ->
  (∀ i, (S i).data? .cls G) ->
  (∀ i, PatternBinders m S (ps i) (ξ i)) ->
  (∀ i, Typing G Δ (ξ i ++ Γ) (ts i) T) ->
  (∀ {q}, Query G q S -> ∃ i, Query.Match q (ps i)) ->
  Typing G Δ Γ (.mtch m n ss ps ts) T
----------------------------------------------------------------------------------------------------
---- Guards
----------------------------------------------------------------------------------------------------
-- | guard :
--   Typing G Δ Γ p A ->
--   Typing G Δ Γ s R ->
--   Typing G Δ Γ t B ->
--   ValidHeadVariable p (is_instty G) ->
--   ValidTyHeadVariable R (is_opent G) ->
--   StableTypeMatch Δ A R ->
--   PrefixTypeMatch Δ A B T ->
--   Typing G Δ Γ (.guard p s t) T
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
  Typing G (K::Δ) (Γ.map (·[+1])) t P ->
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
-- | sym :
--   Typing G Δ Γ t (A ~[K]~ B) ->
--   Typing G Δ Γ (sym! t) (B ~[K]~ A)
-- | seq :
--   Typing G Δ Γ t1 (A ~[K]~ B) ->
--   Typing G Δ Γ t2 (B ~[K]~ C) ->
--   Typing G Δ Γ (t1 `; t2) (A ~[K]~ C)
-- | appc :
--   Typing G Δ Γ f (A ~[K1 -:> K2]~ B) ->
--   Typing G Δ Γ a (C ~[K1]~ D) ->
--   Typing G Δ Γ (f •c a) ((A • C) ~[K2]~ (B • D))
-- | arrowc :
--   Typing G Δ Γ t1 (A ~[.base b1]~ B) ->
--   Typing G Δ Γ t2 (C ~[.base b2]~ D) ->
--   Typing G Δ Γ (t1 -c> t2) ((A -:> C) ~[★]~ (B -:> D))
-- | fst :
--   G&Δ ⊢ C : K1 ->
--   G&Δ ⊢ D : K1 ->
--   Typing G Δ Γ t ((A • C) ~[K2]~ (B • D)) ->
--   Typing G Δ Γ (fst! t) (A ~[K1 -:> K2]~ B)
-- | snd :
--   G&Δ ⊢ C : K1 ->
--   G&Δ ⊢ D : K1 ->
--   Typing G Δ Γ t ((A • C) ~[K2]~ (B • D)) ->
--   Typing G Δ Γ (snd! t) (C ~[K1]~ D)
| allc :
  Typing G (K::Δ) (Γ.map (·[+1])) t (A ~[★]~ B) ->
  Typing G Δ Γ (∀c[K] t) ((∀[K] A) ~[★]~ (∀[K] B))
| apptc :
  Typing G Δ Γ f ((∀[K] A) ~[★]~ (∀[K] B)) ->
  Typing G Δ Γ a (C ~[K]~ D) ->
  A' = A[su C::+0] ->
  B' = B[su D::+0] ->
  Typing G Δ Γ (f •c[a]) (A' ~[★]~ B')
----------------------------------------------------------------------------------------------------
---- Non-determinism
----------------------------------------------------------------------------------------------------
-- | zero :
--   G&Δ ⊢ A : .base b ->
--   Typing G Δ Γ `0 A
-- | choice :
--   G&Δ ⊢ A : K ->
--   Typing G Δ Γ t1 A ->
--   Typing G Δ Γ t2 A ->
--   Typing G Δ Γ (t1 `+ t2) A

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

inductive GlobalWf : List Global -> Global -> Prop where
| data {G : GlobalEnv} {ctors : Fun.Vec (String × SpineTy) n} :
  (∀ i y T, ctors i = (y, T) ->
    SpineKinding (.data 0 x K .nil::G) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
  lookup x G = none ->
  GlobalWf G (.data n x K ctors)
| opent :
  lookup x G = none ->
  GlobalWf G (.odata x K)
| openm {Γ : Vec Ty n} :
  SpineKinding G T ->
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
  Vec.to_list Ts = Γ ->
  G&Δ,Γ ⊢ t : R ->
  GlobalWf G (.inst x p t)
| instty :
  SpineKinding G T ->
  lookup x G = none ->
  GlobalWf G (.octor x T)

inductive ListGlobalWf : List Global -> Prop where
| nil : ListGlobalWf []
| cons : GlobalWf G g -> ListGlobalWf G -> ListGlobalWf (g::G)

notation:175 "⊢ " G:175 => ListGlobalWf G

-- inductive EntryWf : List Global -> Entry -> Prop where
-- | data :
--   lookup x G = some (.data x K ctors) ->
--   EntryWf G (.data x K ctors)
-- | ctor z K (ctors : Vec _ n) (i : Fin n) :
--   lookup z G = some (.data z K ctors) ->
--   ctors[i] = (x, T) ->
--   G&[] ⊢ T : ★ ->
--   ValidCtor z T ->
--   lookup x G = some (.ctor x i T) ->
--   EntryWf G (.ctor x i T)
-- | opent :
--   ValidOpenKind K ->
--   lookup x G = some (odata x K) ->
--   EntryWf G (odata x K)
-- | openm :
--   G&[] ⊢ T : ★ ->
--   lookup x G = some (.openm n x T) ->
--   EntryWf G (.openm n x T)
-- | defn :
--   G&[] ⊢ T : ★ ->
--   G&[],[] ⊢ t : T ->
--   lookup x G = some (.defn x T t) ->
--   EntryWf G (.defn x T t)
-- | instty :
--   ValidInstTy G x [] T ->
--   lookup x G = some (octor x T) ->
--   EntryWf G (octor x T)

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
