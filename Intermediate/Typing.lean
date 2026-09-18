import Intermediate.Global
import Core.Ty
import Surface.Term
import Core.Typing

import Lilac
open Lilac

namespace Intermediate


def Query (G : GlobalEnv) (c : Core.DataConst) (qs : Vec String m) (Ts : Vec Core.Ty m) : Prop :=
  VecTyping (lookup_ctor? G c · ·) qs Ts

inductive Kinding (G : List Intermediate.Global) : List Core.Kind -> Core.Ty -> Core.Kind -> Prop
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

def Ty.data? (c : Core.DataConst) (G : List Global) (A : Core.Ty) : Bool :=
  match A.spine with
  | some (x, _) => is_data c G x
  | none => false


inductive SpineKinding (sv : Core.SpCtorVariant) (x : String) (G : GlobalEnv) (test : Core.Ty -> Bool) : Core.SpineTy -> Prop where
| valid {Ks1 : Vec Core.Kind m1} {Ks2 : Vec Core.Kind m2} {Ts : Vec _ n} :
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  (∀ (i : Fin n), G&Δ ⊢ Ts[i] : ★) ->
  G&Δ ⊢ R : ★ ->
  test R ->
  (sv = .openm -> ∀ (i : Fin n), Intermediate.Ty.data? .opn G Ts[i]) ->
  SpineKinding sv x G test ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩


@[simp, reducible] def method_pattern_size : String × (m : Nat) × Core.Pattern m × Surface.Term -> Nat := λ ⟨_, m, _, _⟩ => m
@[simp, reducible] def method_name : String × (m : Nat) × Core.Pattern m × Surface.Term -> String := λ ⟨s, _, _, _⟩ => s
@[simp, reducible] def spine_pattern_size : Core.SpineTy -> Nat := λ ⟨_, _, _, _, nc, _, _⟩ => nc


inductive GlobalWf : GlobalEnv -> Global -> Prop where
| data {G : GlobalEnv} {ctors : Vec (String × Core.SpineTy) n} :
  (∀ (i : Fin n) y T, ctors[i] = (y, T) ->
    SpineKinding (.data .cls) y ((.data ⟨x, K, ⟨0, #()⟩⟩)::G) (Core.Ty.is_data x) T
    ∧ x ≠ y
    ∧ lookup y G = none) ->
  (∀ i j : Fin n, i ≠ j -> (ctors[i]).1 ≠ (ctors[j]).1) ->
  (lookup x G = none) ->
  GlobalWf G (.data ⟨x, K, ⟨n, ctors⟩⟩)
| defn {G : GlobalEnv} :
  G&[] ⊢ T : ★ ->
  lookup x G = none ->
  GlobalWf G (.defn ⟨x, T, t⟩)
| classDecl {na : Nat} {Ks1 : Vec Core.Kind na}:
  lookup s G = none ->
  (∀ i j: Nat, (hi : i < mτs.length) -> (hj : j < mτs.length) -> i ≠ j -> (mτs[i]'hi).1 ≠ (mτs[j]'hj).1) ->
  (∀ (i : Nat) mn τ, (hi : i < mτs.length) -> mτs[i] = (mn, τ) ->
    SpineKinding Core.SpCtorVariant.openm mn (.classDecl ⟨s, na, Ks1, [],[], []⟩ :: G) (λ _ => true) τ) ->
  (∀ (i : Nat) mn R T (tys : List Core.Ty), (hi : i < mτs.length) ->
   (T.spine = .some (s, tys)) ->
   (tys = (List.range na).reverse.map (t#·)) ->
   mτs[i]'hi = (mn, ⟨na, Ks1, 0, #(), 1, #(T), R⟩) ∧
    mn ≠ s ∧ lookup mn G = none ∧
    G&Ks1.list.reverse ⊢ R : ★) ->
  GlobalWf G (.classDecl ⟨s, na, Ks1, [],[], mτs⟩)

| inst {mτs : List (String × Core.SpineTy)} {mths_impl : List (String × (m : Nat) × Core.Pattern m × Surface.Term)}:
  lookup x G = none ->
  lookup cls_name G = some (.odata cls_name K mτs) ->
  SpineKinding (.data .opn) x G (Ty.data? .opn G) ⟨k1, Ks1, k2, Ks2, k3, As, (gt#cls_name).mkApps_nats (List.range k1).reverse⟩ ->
  (e : mτs.length = mths_impl.length) ->
  (∀ i : Nat, (hi : i < mths_impl.length) ->
    ((mτs[i]).1 = mths_impl[i].1) ∧
    (spine_pattern_size (mτs[i]).2 = method_pattern_size (mths_impl[i]))) ->
  GlobalWf G (.instDecl ⟨x, cls_name, k1, k2, k3, Ks1, Ks2, As, [], [], mths_impl⟩)

inductive ListGlobalWf : List Global -> Prop where
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
        case _ e => subst e; rw [ih] at j2; simp at j2
        case _ e => exact ih
      case inst y T t' j1 j2 => simp [lookup]; sorry; -- exact ih


theorem lookup_weaken {G : GlobalEnv} (wf : ⊢ (g::G)) : lookup x G = some e -> lookup x (g::G) = some e := by
  intro h; apply GlobalWf.drop_lookup_unique 1 wf h

theorem lookup_kind_weaken {G : GlobalEnv} (wf : ⊢ (g::G))
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



theorem Kinding.weaken_global {G : GlobalEnv} (wf : ⊢ (g::G)) : G&Δ ⊢ A : K -> (g::G)&Δ ⊢ A : K
| var h => var h
| global h => global $ lookup_kind_weaken wf h
| arrow j1 j2 => arrow (j1.weaken_global wf) (j2.weaken_global wf)
| all j1 => all (j1.weaken_global wf)
| app j1 j2 => app (j1.weaken_global wf) (j2.weaken_global wf)
| eq j1 j2 => eq (j1.weaken_global wf) (j2.weaken_global wf)



def OpenExhaustive (G : Intermediate.GlobalEnv) : Prop :=
  ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q} {cls},
  Intermediate.lookup x G = some (Intermediate.Entry.openm x cls ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  Intermediate.Query G .opn q Ts ->
  ∃ (i : Nat), ∃ n cls_name k1 k2 k3 Ks1 Ks2 tys fds scs mths, G[i]? = some (.instDecl ⟨n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩)
    ∧ ((∃ (j : Nat), ∃ b p, fds[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p)
       ∨ (∃ (j : Nat), ∃ b p, scs[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p)
       ∨ (∃ (j : Nat), ∃ b p, mths[j]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p))

notation:175 "Ω " G:175 => OpenExhaustive G


inductive EntryWf : Intermediate.GlobalEnv -> Entry -> Prop where
| data :
  lookup x G = some (.data x K ctors) ->
  EntryWf G (.data x K ctors)
| ctor z K (ctors : Vec _ n) (i : Fin n) :
  lookup z G = some (.data z K ctors) ->
  ctors[i] = (x, T) ->
  SpineKinding (.data .cls) x G (Core.Ty.is_data z) T ->
  lookup x G = some (.ctor x i T) ->
  EntryWf G (.ctor x i T)
| odata {n : Nat} {Ks1 : Vec Core.Kind n}:
  lookup x G = some (.odata (n := n) x Ks1 mτs) ->
  (∀ (i : Nat) mn τ, (hi : i < mτs.length) -> mτs[i] = (mn, τ) ->
    SpineKinding Core.SpCtorVariant.openm mn (.classDecl ⟨s, n, Ks1, [],[], []⟩ :: G) (λ _ => true) τ) ->
  EntryWf G (.odata (n := n) x Ks1 mτs)
| defn {G : Intermediate.GlobalEnv}:
  G&[] ⊢ T : ★ ->
  lookup x G = some (.defn x T t) ->
  EntryWf G (.defn x T t)
| octor :
  SpineKinding (.data .opn) x G (Ty.data? .opn G) T ->
  lookup x G = some (.octor x T) ->
  EntryWf G (.octor x T)


theorem EntryWf.from_lookup { G : Intermediate.GlobalEnv} :
  ⊢ G ->
  lookup x G = some e ->
  EntryWf G e
:= by sorry
  -- intro wf h
  -- fun_induction lookup
  -- any_goals try
  --   case _ ih =>
  --     cases wf; case _ h2 wf =>
  --     apply weaken
  --     apply ListGlobalWf.cons wf h2
  --     apply ih h2 h
  -- case _ => cases h
  -- case _ =>
  --   cases h; apply EntryWf.data
  --   simp [lookup]
  -- case _ n y K ctors tl ctors' h1 ih1 =>
  --   have wf' := wf
  --   cases wf; case _ wf gwf =>
  --   cases gwf; case _ h2 h3 h4 =>
  --   simp [Vec.foldr_or_val_some] at h
  --   cases h
  --   case _ lem => sorry -- apply EntryWf.weaken wf' (ih1 wf lem)
  --   case _ lem =>
  --     rcases lem with ⟨i, lem⟩
  --     subst ctors'; simp at lem
  --     rcases lem with ⟨e1, e2⟩; subst e1; simp at *
  --     generalize zdef : ctors[i] = z
  --     rcases z with ⟨z, A⟩
  --     replace h4 := h4 i z A zdef
  --     rw [zdef] at e2; simp at e2; subst e2
  --     rcases h4 with ⟨q1, q2, q3⟩
  --     apply EntryWf.ctor y K ctors
  --     simp [lookup]; exact zdef
  --     apply SpineKinding.weaken_global_ctors wf' q1
  --     simp [lookup]; split; simp_all; rw [q3]
  --     apply EntryWf.from_lookup_ctor2; simp
  --     exists i; rw [zdef]; simp
  --     intro j j1 j2
  --     replace h3 := h3 j i j1
  --     subst j2; grind
  -- case _ =>
  --   cases h; apply EntryWf.odata
  --   simp [lookup]
  -- case _ =>
  --   have wf' := wf
  --   cases h; cases wf; case _ wf h =>
  --   cases h; case _ j1 j2 =>
  --   apply EntryWf.openm
  --   apply SpineKinding.weaken_global (tst := λ _ _ => true) wf' (by simp) j2
  --   simp [lookup]
  -- case _ =>
  --   have wf' := wf
  --   cases h; cases wf; case _ wf h =>
  --   cases h; case _ j1 j2 =>
  --   apply EntryWf.defn
  --   apply Kinding.weaken_global wf' j1
  --   apply Typing.weaken_global wf' j2
  --   simp [lookup]
  -- case _ =>
  --   have wf' := wf
  --   cases h; cases wf; case _ wf h =>
  --   cases h; case _ j1 j2 =>
  --   apply EntryWf.octor
  --   apply SpineKinding.weaken_global wf' _ j2
  --   intro A h; apply Ty.data?_global_weaken wf' h
  --   simp [lookup]



theorem lookup_none_ctor? {Γ : Intermediate.GlobalEnv} (wf : ⊢ Γ) :
  Intermediate.lookup s Γ = none ->
  Intermediate.lookup q Γ = some w ->
  Intermediate.Entry.ctor? s Core.DataConst.opn w = true  ->
  False
:= by
  intro h1 h2 h3
  simp [Intermediate.Entry.ctor?] at h3
  cases w <;> simp at h3
  case _ q spty =>
  rcases spty with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
  simp at h3; split at h3 <;> simp at h3
  subst h3; case _ h3 =>
  have e := Intermediate.lookup_name_agrees h2; simp [Intermediate.Entry.name] at e; subst e
  have lem2 := EntryWf.from_lookup wf h2
  cases lem2; case _ lem1 lem2 =>
  cases lem1; case _ Δ c2 c3 c4 c5 c6 =>
  subst Δ;
  unfold Ty.data? at c6; simp [h3, is_data, h1] at c6;


end Intermediate
