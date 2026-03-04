import Core.Ty
import Core.Term
import Surface.Ty
import Surface.Term
import Core.Typing

import Translation.Ty
open LeanSubst


def Core.Ty.synth_term (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :  Core.Ty -> Option Core.Term
| _ => none

def Core.Ty.synth_coercion (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
  Core.Ty -> Core.Ty -> Option Core.Term
| _, _ => none

inductive Core.Translation.SynthTerm (G' : Core.GlobalEnv) (Δ' : Core.KindEnv) (Γ' : Core.TyEnv) :
  Core.Ty -> Core.Term -> Prop where
| refl :
  Core.Translation.SynthTerm G' Δ' Γ' (T ~[★]~ T) (refl! T)
| sym :
  Core.Translation.SynthTerm G' Δ' Γ' (T ~[★]~ T') c ->
  Core.Translation.SynthTerm G' Δ' Γ' (T' ~[★]~ T) (sym! c)
| trans :
  Core.Translation.SynthTerm G' Δ' Γ' (T ~[★]~ T') c1 ->
  Core.Translation.SynthTerm G' Δ' Γ' (T' ~[★]~ T'') c2 ->
  Core.Translation.SynthTerm G' Δ' Γ' (T' ~[★]~ T) (c1 `; c2)



inductive Mode : Type where | chk | inf

inductive Surface.Term.Elab (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) : Mode ->
  Surface.KindEnv -> Surface.TyEnv -> Surface.Term -> Surface.Ty ->
  Core.Term -> Prop where
| var  {Γ : Surface.TyEnv} :
  Γ[x]? = some T ->
  Translation.Ty G Δ T `★ T' ->
  Surface.Term.Elab G G' inf Δ Γ `#x T #x
| global :
  Surface.lookup_type G x = some T ->
  Translation.Ty G Δ T `★ T' ->
  Surface.Term.Elab G G' inf Δ Γ g`#x T g#x
| app_arr :
  Translation.Ty G Δ A `★ A' ->
  Surface.Term.Elab G G' inf Δ Γ f (A `-:> B) f' ->
  Surface.Term.Elab G G' chk Δ Γ a A a' ->
  Surface.Term.Elab G G' inf Δ Γ (f `• a) B (f' • a')
| app_then :
  Translation.Ty G Δ A `◯ A' ->
  Surface.Term.Elab G G' inf Δ Γ f (A `=:> B) f' ->
  Core.Translation.SynthTerm G' Δ.translate Γ.translate A.translate a' ->
  Surface.Term.Elab G G' inf Δ Γ f B (f' ∘[ a' ])
| appt :
  Translation.Ty G Δ A K A' ->
  Surface.Term.Elab G G' inf Δ Γ e (`∀[K]P) e' ->
  P' = P[su A::+0] ->
  Surface.Term.Elab G G' inf Δ Γ (e `•[ A ]) P' (e' •[ A' ])

| lam :
  Translation.Ty G Δ A `★ A' ->
  Surface.Term.Elab G G' chk Δ (A::Γ) t B t' ->
  Surface.Term.Elab G G' chk Δ Γ (λˢ[A] t) (A `-:> B) (λ[A'] t')
| lamt :
  Translation.Ty G (K::Δ) P `★ P' ->
  Surface.Term.Elab G G' chk (K::Δ) (Γ.map (·[+1])) t P t' ->
  Surface.Term.Elab G G' chk Δ Γ (Λˢ[K] t) (`∀[K] P) (Λ[K.translate] t')

| mtch (CTy : Vect n Surface.Ty) (CTy' : Vect n Core.Ty)
       (PTy : Vect n Surface.Ty) (PTy' : Vect n Core.Ty)
       (pats : Vect n Surface.Term) (pats' : Vect n Core.Term)
       (cs : Vect n Surface.Term) (cs' : Vect n Core.Term) :
  Surface.Term.Elab G G' inf Δ Γ s R s' ->
  ValidTyHeadVariable R (is_data G) ->
  Surface.Term.Elab G G' inf  Δ Γ c T c' -> -- catch all term is of type T
  (∀ i, ValidHeadVariable (pats i) (is_ctor G)) -> -- patterns are of the right shape
  (∀ i, Surface.Term.Elab G G' chk Δ Γ (pats i) (PTy i) (pats' i)) -> -- each pattern has a type
  (∀ i, StableTypeMatch Δ (PTy i) R) -> -- the pattern type has a return type that matches datatype
  (∀ i, Surface.Term.Elab G G' chk Δ Γ (cs i) (PTy i) (cs' i)) -> -- each case match has a type
  (∀ i, PrefixTypeMatch Δ (PTy i) (CTy i) T) -> -- patten type and case type
  Surface.Term.Elab G G' chk Δ Γ (matchˢ! n R s pats cs c) T (match! n s' pats' cs' c')

| annot :
  Surface.Term.Elab G G' inf Δ Γ t T t' ->
  Surface.Term.Elab G G' chk Δ Γ (.annot t T) T t'

| subsump :
  Surface.Term.Elab G G' inf Δ Γ t Tinf t' ->
  Surface.Translation.Ty G Δ T `★ T' ->
  Core.Translation.SynthTerm G' Δ.translate Γ.translate (Tinf.translate ~[★]~  T') c ->
  Surface.Term.Elab G G' chk Δ Γ t T (t' ▹ c)

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
| .match (n := n) _ s ps cs d => do
  let s' <- s.translate G Δ Γ
  let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
  let ps' <- ops'.seq
  let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
  let cs' <- ocs'.seq
  let d' <- d.translate G Δ Γ
  return match! n s' ps' cs' d'
| .annot t _ => do
  t.translate G Δ Γ



-- @[simp, grind]
def Surface.Term.type_directed_translate
  (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Surface.Ty) :
  Surface.Term -> Option Core.Term
| `#x =>
  match Γ[x]? with
  | some τ' => do
    let c <- (τ' ~[★]~ τ.translate).synth_term G Δ Γ
    return (#x ▹ c)
  | _ => none

| g`#x =>
  match Core.lookup_type G x with
  | some τ' => do
    let c <- (τ' ~[★]~ τ.translate).synth_term G Δ Γ
    return (g#x ▹ c)
  | _ =>  none
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
| .match (n := n) R s ps cs d => do
  let s' <- s.type_directed_translate G Δ Γ R
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
def Surface.Ty.prefix_type_match (Δ : List Kind) : Ty -> Ty -> Option Ty
  | (.arrow A B), (.arrow A' B') => do
    if A == A'
    then prefix_type_match Δ B B'
    else none

  | (.all K A), (.all K' A') => do
    if K == K'
    then let x <- prefix_type_match (K :: Δ) A A'
         if x[-1][+1] == x
         then return x[-1]
         else none
    else none
  | A, T => do
    let _ <- A.spine
    return T

def Surface.Ty.stable_type_match : List Kind -> Ty -> Ty -> Option Unit
| Δ, (.all K A), R => Ty.stable_type_match (K::Δ) A R[+1]
| Δ, (.arrow _ B), R => Ty.stable_type_match Δ B R
| _, A, R =>
 do
  let _ <- R.spine
  if A == R
  then some ()
  else none



mutual

  def Surface.Term.type_inf_translate
    (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv):
    Surface.Term -> Option (Core.Term × Surface.Ty)

  | `#x => do
    let τ <- Γ[x]?
    return (#x, τ)
  | g`#x => do
    let τ <- Surface.lookup_type G x
    return (g#x, τ)
  | .annot t τt => do
    let t' <- t.type_chk_translate G G' Δ Γ τt
    return (t' , τt)
  | .appt f a => do
    let (f', T) <- f.type_inf_translate G G' Δ Γ
    match T with
    | .all K T =>
      -- ensure a has kind K?
      return (f' •[ a.translate ], T[su a ::+0])
    | _ => none
  | _ => none



  def Surface.Term.type_chk_translate
    (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) (τ : Surface.Ty) :
    Surface.Term -> Option Core.Term

  | .lamt K t => do
    match τ with
    | .all K' τ' =>
      let t' <- t.type_chk_translate G G' (K::Δ) (Γ.map (·[+1])) τ'
      if K' == K then return (Λ[K.translate] t') else none
    | _ => none
  | .lam A' t => do
    match τ with
    | .arrow A B =>
      let t' <- t.type_chk_translate G G' Δ (A::Γ) B
      if A == A' then return λ[A.translate] t' else none
    | _ => none

  | .match (n := n) R s ps cs d => do
    let s' <- s.type_chk_translate G G' Δ Γ R
    let ops' : Vect n (Option (Core.Term × Ty)) := (λ i => (ps i).type_inf_translate G G' Δ Γ)
    let ps' <- ops'.seq
    let ocs' : Vect n (Option (Core.Term × Ty)) := (λ i => (cs i).type_inf_translate G G' Δ Γ)
    let cs' <- ocs'.seq
    let _ <- R.valid_data_type G
    let ops' : Vect n (Option Unit) := λ i => Ty.stable_type_match Δ (ps' i).snd R
    let _ <- ops'.seq
    let ostm : Vect n (Option Ty) :=  λ i => Ty.prefix_type_match Δ ((ps' i).snd) (cs' i).snd
    let _ <- ostm.seq
    let d' <- d.type_chk_translate G G' Δ Γ τ
    match! n s' ((λ x => x.fst) <$> ps') ((λ x => x.fst) <$> cs') d'
  | _ => none

end

@[simp]
abbrev ElabArgs : Mode -> Type
| .inf => Option (Core.Term × Surface.Ty)
| .chk => Surface.Ty -> Option (Core.Term)

def elab_term (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) (t : Surface.Term) : (m : Mode) -> ElabArgs m
| .inf => Surface.Term.type_inf_translate G G' Δ Γ t
| .chk => λ (τ : Surface.Ty) => Surface.Term.type_chk_translate G G' Δ Γ τ t
