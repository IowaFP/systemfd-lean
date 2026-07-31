import Surface.Global
import Core.Global
import Intermediate.Global

import Surface.Typing

import Translation.Ty
import Translation.Term

import Lilac

open LeanSubst


namespace Translation

-- Kind check the types, leaves the terms as surface
def translate_SI : Surface.GlobalEnv -> Option Intermediate.GlobalEnv := List.foldrM (init := []) (λ g Γ =>
  match g with
  | .data (n := n) s K ctors =>
    return .cons (.data n s ⟦ K ⟧  (ctors.map (λ (s, ⟨n1, v1, n2, v2, n3, v3, R⟩) => (s, sorry)))) Γ
  | .defn s T t => sorry
  | .classDecl s Ks fds mτs => sorry
  | .instDecl iname clname iτs ts => sorry
)



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
         let t' <- t.type_directed_translate acc (Δ ++ ζ) Γ R⟨Ren.add Core.Ty ζ.length⟩
         return .cons (.inst s p t') acc
    else none
  | _ => none)


-- def Intermediate.OpenExhaustive (G : List Global) : Prop :=
--   ∀ {x na nb nc} {Ks1 : Vec _ na} {Ks2 : Vec _ nb} {Ts : Vec _ nc} {R q},
--   lookup x G = some (.openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
--   Query G .opn q Ts ->
--   ∃ (i : Nat), ∃ b p, G[i]? = some (.inst x p b) ∧ Query.Match q p


-- theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} :
--   translate_SI G = some G' ->
--   Core.OpenExhaustive G' := by sorry

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
