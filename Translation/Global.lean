import Surface.Global
import Core.Global
import Intermediate.Global

import Surface.Typing
import Intermediate.Typing

import Translation.Ty
import Translation.Term

import Lilac

open Lilac
open LeanSubst

namespace Translation


-- Kind check the types, leaves the terms untouched
def translate_SI : Surface.GlobalEnv -> Option Intermediate.GlobalEnv := List.foldrM (init := []) (λ g Γ =>
  match g with
  | .data (n := n) s K ctors => do
    let ctors' : Lilac.Vec (String × Core.SpineTy) n :=
      ctors.map (λ (s, ⟨n1, v1, n2, v2, n3, v3, R⟩) => (s, ⟨n1, v1.map (·.translate) , n2, v2.map (·.translate), n3, v3.map (·.translate), ⟦R⟧⟩))
    return .cons (.data n s ⟦ K ⟧ ctors') Γ
  | .defn s T t => return .cons (.defn s ⟦T⟧ t) Γ
  | .classDecl s sups Ks fds mτs => none
    -- sorry
  | .instDecl iname spTy ts => none -- sorry
)


def Intermediate.OpenExhaustive (G : Intermediate.GlobalEnv) : Prop :=
  ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q},
  Intermediate.lookup x G = some (Intermediate.Entry.openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  Intermediate.Query G .opn q Ts ->
  ∃ (i : Nat), ∃ b p, G[i]? = some (.inst x p b) ∧ Core.Query.Match q p

def translate_IC : Intermediate.GlobalEnv -> Option Core.GlobalEnv := List.foldrM (init := []) (λ g acc =>
  match g with
| (.data n s K ctors) => do
  return (.data n s K ctors) :: acc
| .defn n T t => do
  let t' : Core.Term <- Surface.Term.type_directed_translate acc [] [] T t
  return (.defn n T t') :: acc
| .odata s K => do
  return .cons (.odata s K) acc
| .openm s spTy => do
  return .cons (.openm s spTy) acc
| .octor s spTy => do
  return .cons (.octor s spTy) acc
| .inst (m := m) s p t =>
  match Core.lookup s acc with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) => do
    let Δ := (Ks1.list ++ Ks2.list).reverse
    if s == y && m == n
    then let ⟨ζ, Γ⟩ <- Core.pattern_binders (.data .opn) acc Δ n Ts p
         let t' <- t.type_directed_translate acc (Δ ++ ζ) Γ R[Subst.add Core.Ty ζ.length]
         return .cons (.inst s p t') acc
    else none
  | _ => none)


theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} :
  --
  translate_SI G = some G' ->
  Intermediate.OpenExhaustive G' := by
intro h
unfold translate_SI at h
intro x na nb nc Ks1 Ks2 Ts R q h1 h2

sorry

theorem translate_IC_indexing_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} :
  translate_IC G = some G' ->
  G'[i]? = some (Core.Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  G[i]? = some (Intermediate.Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩)
   := by
intro h1 h2
unfold translate_IC at h1
simp at h1 h2
sorry

theorem translate_IC_indexing_inst {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} :
  translate_IC G = some G' ->
  G[i]? = some (Intermediate.Global.inst x p b) ->
  ∃ b', G'[i]? = some (Core.Global.inst x p b')
   := by
intro h1 h2
unfold translate_IC at h1
simp at h1 h2
sorry



theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  translate_IC G = some G' ->
  Core.lookup x G' = some (Core.Entry.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  Intermediate.lookup x G = some (Intermediate.Entry.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) := by
intro h1 h2
unfold translate_IC at h1
simp at h1 h2
sorry



theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  translate_IC G = some G' ->
  Core.Query G' Core.DataConst.opn q Ts ->
  Intermediate.Query G Intermediate.DataConst.opn q Ts := by
intro h1 h2
unfold translate_IC at h1
simp at h1 h2

sorry


theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  Intermediate.OpenExhaustive G ->
  translate_IC G = some G' ->
  Core.OpenExhaustive G' := by
intro oe h1
intro x na nb nc Ks1 Ks2 Ts R q h2 h3
simp at h1 h2 h3
have lem1 := translate_IC_lookup_openm h1 h2
have lem2 := translate_IC_query h1 h3
replace oe := @oe x na nb nc Ks1 Ks2 Ts R q lem1 lem2
rcases oe with ⟨i, b, p, oe1, oe2⟩
have lem3 := translate_IC_indexing_inst h1 oe1
rcases lem3 with ⟨b', lem3⟩
exists i; exists b'; exists p

-- inductive Translation.GlobalWf : Surface.GlobalEnv -> Core.GlobalEnv -> Surface.Global -> Prop where
-- | data {ctors : Vect n (String × Surface.Ty)} {G : Surface.GlobalEnv}{G' : Core.GlobalEnv}:
--   (∀ i y T, ctors i = (y, T) ->
--     (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidCtor x T
--     ∧ x ≠ y
--     ∧ Surface.lookup y G = none) ->
--   (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
--   Surface.lookup x G = none ->
--   GlobalWf G G' (Surface.Global.data x K ctors)
-- | defn :
--   Surface.lookup x G = none ->
--   G&[] ⊢s T : `★ ->
--   Surface.Term.Elab G G' .chk [] [] t T t' ->
--   GlobalWf G G' (Surface.Global.defn x T t)
-- | classDecl :
--   Surface.lookup s G = none ->
--   Surface.ValidOpenKind K ->
--   (∀ i j, (ms i).1 ≠ (ms j).1) ->
--   (∀ i y T, ms i = (y, T) ->
--     (Surface.Global.classDecl s K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidClassMethodTy s T
--     ∧ s ≠ y
--     ∧ Surface.lookup y G = none) ->
--   GlobalWf G G' (Surface.Global.classDecl s K ms)
-- | instDecl :
--   Surface.ValidClassInstTy C T ->
--   -- TODO: Do Non-overlapping check here
--   Surface.lookup C G = some (.opent C K ms') ->
--   -- TODO: check for method types
--   GlobalWf G G' (.instDecl T ms)


-- inductive ValidClassDecl (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (x : String) (K: Surface.Kind) :
--           {n : Nat} -> (Vect n (String × Surface.Ty)) -> Core.GlobalEnv -> Prop where
-- | nil :
--   Surface.lookup x G = none ->
--   Surface.ValidOpenKind K ->
--   ValidClassDecl G G' x K Vect.nil (List.cons (.opent x K.translate) G')
-- | cons {n : Nat} {ms : Vect n (String × Surface.Ty)} {m : String} {τ : Surface.Ty} :
--   ms' = ms.to_list.map (λ (x, τ) => Core.Global.openm x τ.translate) ->
--   ValidClassDecl G G' x K ms (ms' ++ List.cons (.opent x K.translate) G')  ->

--   -- method names are unique
--   Surface.lookup m (.classDecl x K ms :: G) = none ->

--   -- method type is okayg
--   Surface.ValidClassMethodTy x τ ->
--   (.classDecl x K ms :: G)&[] ⊢s τ : `★ ->

--   ValidClassDecl G G' x K (n := n + 1)
--                  (Vect.cons (m , τ) ms)
--                  (List.cons (Core.Global.openm m τ.translate)
--                  (ms' ++ List.cons (.opent x K.translate) G'))


-- inductive ValidInstDecl (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) :
--           Ty -> Vect n (String × Surface.Term) -> Core.GlobalEnv -> Prop where



-- inductive Surface.Global.Elab : Surface.GlobalEnv -> Core.GlobalEnv -> Prop
-- | nil : Surface.Global.Elab [] []

-- | defn :
--   Surface.Global.Elab G G' ->

--   Surface.lookup x G = none ->
--   G&[] ⊢s T : `★ ->
--   Surface.Term.Elab G G' .chk [] [] t T t' ->

--   Surface.Global.Elab (.cons (.defn x T t) G) ((.defn x (T.translate) t') :: G')

-- | data {n : Nat} {ctors : Vect n (String × Ty)} {ctors' : Vect n (String × Core.Ty)} :
--   Surface.Global.Elab G G' ->

--   (∀ i y T, ctors i = (y, T) ->
--     (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidCtor x T
--     ∧ x ≠ y
--     ∧ Surface.lookup y G = none) ->
--   (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
--   Surface.lookup x G = none ->

--   ctors' = (λ i => ((ctors i).1 , (ctors i).2.translate)) ->

--   Surface.Global.Elab (.cons (.data (n := n) x K ctors) G) (.cons (.data n x K.translate ctors') G')

-- | classDecl {n : Nat} {ms : Vect n (String × Ty)} {Δ : Core.GlobalEnv} :
--   Surface.Global.Elab G G' ->
--   ValidClassDecl G G' x K ms Δ ->
--   Surface.Global.Elab ((.classDecl x K ms) :: G) Δ

-- | instDecl {n} {ms : Vect n (String × Term)} {Δ : Core.GlobalEnv} :
--   Surface.Global.Elab G G' ->
--   ValidInstDecl G G' τ ms Δ ->
--   Surface.Global.Elab G Δ


-- notation:170 G:170 " -↪ " G':170 => Surface.Global.Elab G G'


end Translation
