import Core.Ty
import Core.Term
import Surface.Ty
import Surface.Term

import Translation.Ty
open LeanSubst


def Core.Ty.synth_term (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :  Core.Ty -> Option Core.Term
| _ => none

def Core.Ty.synth_coercion (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
  Core.Ty -> Core.Ty -> Option Core.Term
| _, _ => none

inductive Core.Translation.SynthTerm (G' : Core.GlobalEnv) (Δ' : Core.KindEnv) (Γ' : Core.TyEnv) :
  Core.Ty -> Core.Term -> Prop where


inductive Surface.Translation.Term (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) :
  Surface.KindEnv -> Surface.TyEnv -> Surface.Term -> Surface.Ty ->
  Core.KindEnv -> Core.TyEnv -> Core.Term -> Core.Ty -> Prop where
| var  {Γ : Surface.TyEnv} :
  Γ[x]? = some (A `=:> T) ->
  Γ'[x]? = some (.arrow A' T') ->
  Translation.Ty G G' Δ T `★ Δ' T' ★ ->
  Translation.Ty G G' Δ A `◯ Δ' A' ◯ ->
  Core.Translation.SynthTerm G' Δ' Γ' A' d ->
  Translation.Term G G' Δ Γ `#x T Δ' Γ' (#x ∘[ d ])  T'
| global :
  Surface.lookup_type G x = some T ->
  Core.lookup_type G' x = some T' ->
  Translation.Ty G G' Δ T `★ Δ' T' ★ ->
  Translation.Term G G' Δ Γ g`#x T Δ' Γ' g#x T'
| app :
  Translation.Ty G G' Δ A `★ Δ' A' ★ ->
  Translation.Term G G' Δ Γ f (A `-:> B) Δ' Γ' f' (A' -:> B') ->
  Translation.Term G G' Δ Γ a A Δ' Γ' a' A' ->
  Translation.Term G G' Δ Γ f (A `-:> B) Δ' Γ' f' B'
| appP :
  Translation.Ty G G' Δ A `◯ Δ' A' ◯ ->
  Translation.Term G G' Δ Γ f (A `=:> B) Δ' Γ' f' (A' -:> B') ->
  Core.Translation.SynthTerm G' Δ' Γ' A' a' ->
  Translation.Term G G' Δ Γ f B Δ' Γ' (f' ∘[ a' ]) B'
| lam :
  Translation.Ty G G' Δ A `★ Δ' A' ★ ->
  Translation.Term G G' Δ (A::Γ) t B Δ' (A'::Γ') t' B' ->
  Translation.Term G G' Δ Γ (λˢ[A] t) (A `-:> B) Δ' Γ' (λ[A'] t') (A' -:> B')
| mtch (CTy : Vect n Surface.Ty) (CTy' : Vect n Core.Ty)
       (PTy : Vect n Surface.Ty) (PTy' : Vect n Core.Ty)
       (pats : Vect n Surface.Term) (pats' : Vect n Core.Term)
       (cs : Vect n Surface.Term) (cs' : Vect n Core.Term) :
  Translation.Term G G' Δ Γ s R Δ' Γ' s' R' ->
  ValidTyHeadVariable R (is_data G) ->
  Translation.Term G G' Δ Γ c T Δ' Γ' c' T' -> -- catch all term is of type T
  (∀ i, ValidHeadVariable (pats i) (is_ctor G)) -> -- patterns are of the right shape
  (∀ i, Translation.Term G G' Δ Γ (pats i) (PTy i) Δ' Γ' (pats' i) (PTy' i)) -> -- each pattern has a type
  (∀ i, StableTypeMatch Δ (PTy i) R) -> -- the pattern type has a return type that matches datatype
  (∀ i, Translation.Term G G' Δ Γ (cs i) (PTy i) Δ' Γ' (cs' i) (CTy' i)) -> -- each case match has a type
  (∀ i, PrefixTypeMatch Δ (PTy i) (CTy i) T) -> -- patten type and case type
  Translation.Term G G' Δ Γ (matchˢ! s pats cs c) T Δ' Γ' (match! n s' pats' cs' c') T'
| lamt :
  Translation.Ty G G' (K::Δ) P `★ (K.translate::Δ') P' ★ ->
  Translation.Term G G' (K::Δ) (Γ.map (·[+1])) t P (K.translate :: Δ') (Γ'.map (·[+1])) t' P' ->
  Translation.Term G G' Δ Γ (Λˢ[K] t) (`∀[K] P) Δ' Γ' (Λ[K.translate] t') (∀[K.translate] P')
| annot :
  Translation.Ty G G' Δ Ta `★ Δ' Ta' ★ ->
  Translation.Ty G G' Δ Tb `★ Δ' Tb' ★ ->
  Core.Translation.SynthTerm G' Δ' Γ' (Ta' ~[★]~ Tb') c ->
  Translation.Term G G' Δ Γ t Ta Δ' Γ' t' Ta' ->
  Translation.Term G G' Δ Γ (.annot t Ta) Tb Δ' Γ' (t' ▹ c) Tb'


@[simp, grind]
def Surface.Term.translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
  Surface.Term -> Option Core.Term
| `#x => #x
| g`#x => g#x
| .lamt K t => do
  let t' <- t.translate G (K.translate :: Δ) (Γ.map (·[+1]))
  return (Λ[K.translate] t')
| .lam A t => do
  let t' <- t.translate G Δ (A.translate :: Γ)
  return λ[A.translate] t'
| .app t1 t2 => do
  let t1' <- t1.translate G Δ Γ
  let t2' <- t2.translate G Δ Γ
  return (t1' • t2')
| .appt t1 t2 => do
  let t1' <- t1.translate G Δ Γ
  let t2' <- t2.translate
  return (t1' •[ t2' ])
| .match (n := n) s ps cs d => do
  let s' <- s.translate G Δ Γ
  let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
  let ps' <- ops'.seq
  let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
  let cs' <- ocs'.seq
  let d' <- d.translate G Δ Γ
  return match! n s' ps' cs' d'
| .annot t _ => do
  t.translate G Δ Γ
| .hole T => T.translate.synth_term G Δ Γ


-- @[simp, grind]
def Surface.Term.type_directed_translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Surface.Ty):
  Surface.Term -> Option Core.Term
| `#x => do
  match τ with
  | .then A B =>
    let d <- Core.Ty.synth_term G Δ Γ A.translate
    return (#x ∘[d])
  | _ => none

| g`#x => do
  match τ with
  | .then A B =>
    let d <- Core.Ty.synth_term G Δ Γ A.translate
    return (g#x ∘[d])
  | _ => none

  -- match Γ[x]? with
  -- | some τ' =>
  --   if τ.translate == τ' then return #x else none
  -- | _ =>  none
| .lamt K t => do
  match τ with
  | .all K' τ' =>
    let t' <- t.type_directed_translate G (K.translate :: Δ) (Γ.map (·[+1])) τ'
    if K == K' then return (Λ[K.translate] t') else none
  | _ => none
| .lam A t => do
  match τ with
  | .arrow A' B =>
    let t' <- t.type_directed_translate G Δ (A.translate :: Γ) B
    if A == A' then return λ[A.translate] t' else none
  | _ => none
-- Elimination forms are a little annoying
| .match (n := n) (annot s sτ) ps cs d => do -- also maybe store the type of the scrutinee to eliminate
  let s' <- s.type_directed_translate G Δ Γ sτ
  let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
  let ps' <- ops'.seq
  let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
  let cs' <- ocs'.seq
  let d' <- d.type_directed_translate G Δ Γ τ
  return match! n s' ps' cs' d'
| .annot t τt => do
  let t' <- t.type_directed_translate G Δ Γ τt
  let c <- Core.Ty.synth_coercion G Δ Γ τt.translate τ.translate
  return t' ▹ c
| _ => none


-- | t =>
--   match sp_prf : t.spine with
--   | some (x, sp) => do
--     let sp := sp.attach

--     let hτ <- Core.lookup_type G x
--     let (t', r) <- List.foldlM (λ (acct, τ) x =>
--                match τ, x with
--                | .all K τ, ⟨.type A, prf⟩ =>
--                  -- K better be kind of A, but we can't do that yet.
--                  let A' := A.translate
--                  let σ : Subst Core.Ty := (su A')::+0
--                  return (acct •[ A' ], τ[σ])
--                | .arrow A B, ⟨.term t, prf⟩ => do
--                  let t' <- t.type_directed_translate G Δ Γ A
--                  return (acct • t', B)
--                | _ , _ => none)
--                (g#x, hτ) sp
--     if r == τ.translate then return t' else none
--   | none => none
-- termination_by t => t.size
-- decreasing_by (
-- all_goals try (simp at *)
-- · omega
-- · omega
-- · have lem := Spine.elem_size_le_term sp_prf (.term t) prf; simp [SpineElem.size] at lem; exact lem
-- )
