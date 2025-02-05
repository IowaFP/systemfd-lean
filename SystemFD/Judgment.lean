import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx

inductive JudgmentVariant where
| wf | prf

@[simp]
abbrev JudgmentArgs : JudgmentVariant -> Type
| .wf => Unit
| .prf => Term × Term

inductive Judgment : (v : JudgmentVariant) -> Ctx Term -> JudgmentArgs v -> Prop where
--------------------------------------------------------------------------------------
---- Well-Formed Contexts
--------------------------------------------------------------------------------------
| empty :  Judgment .wf [] ()
| wftype :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.type A::Γ) ()
| wfkind :
  Judgment .prf Γ (A, .kind) ->
  Judgment .wf Γ () ->
  Judgment .wf (.kind A::Γ) ()
| wfdatatype :
  Judgment .prf Γ (A, .kind) ->
  Judgment .wf Γ () ->
  Judgment .wf (.datatype A::Γ) ()
| wfctor :
  Judgment .prf Γ (A, ★) ->
  Judgment .wf Γ () ->
  valid_ctor Γ ->
  Judgment .wf (.ctor A::Γ) ()
| wfopent :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.opent A::Γ) ()
| wfopenm :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.openm A::Γ) ()
| wfinsttype :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.insttype A::Γ) ()
| wfinst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t, T) ->
  Judgment .wf (.inst x t::Γ) ()
--------------------------------------------------------------------------------------
---- Declarations
--------------------------------------------------------------------------------------
| letdata :
  Judgment .prf Γ (T, .kind) ->
  Judgment .prf (.datatype T::Γ) (t, A) ->
  Judgment .prf Γ (.letdata T t, A)
| letctor :
  Judgment .prf Γ (T, ★) ->
  valid_ctor Γ ->
  Judgment .prf (.ctor T::Γ) (t, A) ->
  Judgment .prf Γ (letctor! T t, A)
| letopentype :
  Judgment .prf Γ (T, .kind) ->
  Judgment .prf (.opent T::Γ) (t, A) ->
  Judgment .prf Γ (letopentype! T t, A)
| letopen :
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf (.openm T::Γ) (t, A) ->
  Judgment .prf Γ (letopen! T t, A)
| insttype :
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf (.insttype T::Γ) (t, A) ->
  Judgment .prf Γ (insttype! T t, A)
| inst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t1, T) ->
  Judgment .prf (.inst x t1::Γ) (t2, A) ->
  Judgment .prf Γ (.inst x t1 t2, A)
--------------------------------------------------------------------------------------
---- Kind/Type Constructor Judgments
--------------------------------------------------------------------------------------
| ax :
  Judgment .wf Γ () ->
  Judgment .prf Γ (.const K, .kind)
| var_type :
  Judgment .wf Γ () ->
  .some T = Frame.get_type (Γ d@ x) ->
  Judgment .prf Γ (#x, T)
| allk :
  Judgment .prf Γ (A, .kind) ->
  Judgment .prf Γ (B, .kind) ->
  Judgment .prf Γ (A -k> B, .kind)
| allt :
  Judgment .prf Γ (A, .kind) ->
  Judgment .prf (.kind A::Γ) (B, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (∀[A] B, K)
| arrow :
  Judgment .prf Γ (A, .const K1) ->
  Judgment .prf Γ (B, .const K2) ->
  Judgment .prf Γ (A -t> B, .const K2)
| appk :
  Judgment .prf Γ (f, A -k> B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@k a, B)
--------------------------------------------------------------------------------------
---- Datatype case expressions
--------------------------------------------------------------------------------------
| ite :
  Judgment .prf Γ (p, A) ->
  (τ, sR) = Term.to_telescope A ->
  [S' τ.length]R = sR ->
  .some (ctorid, _) = Term.neutral_form p ->
  .some (dataid, _) = Term.neutral_form R ->
  is_datatype Γ ctorid dataid ->
  Judgment .prf Γ (R, ★) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (i, B) ->
  (τ', sT) = Term.to_telescope B ->
  .some ξ = prefix_equal τ τ' ->
  sT' = Term.from_telescope ξ sT ->
  [S' τ.length]T = sT' ->
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf Γ (e, T) ->
  Judgment .prf Γ (.ite p s i e, T)
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard :
--   .some openmid = Term.neutral_head s -> // Check that it's actually an open method?
  Judgment .prf Γ (p, A) ->
  (τ, sR) = Term.to_telescope A ->
  [S' τ.length]R = sR ->
  Judgment .prf Γ (R, ◯) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (t, B) ->
  (τ', sT) = Term.to_telescope B ->
  .some ξ = prefix_equal τ τ' ->
  sT' = Term.from_telescope ξ sT ->
  [S' τ.length]T = sT' ->
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf Γ (.guard p s t, T)
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  Judgment .prf Γ (A, .const K) ->
  Judgment .prf (.type A::Γ) (t, B) ->
  Judgment .prf Γ (`λ[A] t, A -t> B)
| app :
  Judgment .prf Γ (f, A -t> B) ->
  Judgment .prf Γ (a, A) ->
  B' = B β[.kind] ->
  Judgment .prf Γ (f `@ a, B')
| lamt :
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf (.kind A::Γ) (t, B) ->
  Judgment .prf Γ (Λ[A] t, ∀[A] B)
| appt :
  Judgment .prf Γ (f, ∀[A] B) ->
  Judgment .prf Γ (a, A) ->
  B' = B β[a] ->
  Judgment .prf Γ (f `@t a, B')
| cast :
  Judgment .prf Γ (t, A) ->
  Judgment .prf Γ (c, A ~ B) ->
  Judgment .prf Γ (t ▹ c, B)
--------------------------------------------------------------------------------------
---- Coercions
--------------------------------------------------------------------------------------
| refl :
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (refl! A, A)
| sym :
  Judgment .prf Γ (t, A ~ B) ->
  Judgment .prf Γ (sym! t, B ~ A)
| seq :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, B ~ C) ->
  Judgment .prf Γ (t1 `; t2, A ~ C)
| appc :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c t2, (A `@k C) ~ (B `@k D))
| arrowc :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 -c> t2, (A -t> C) ~ (B -t> D))
| fst :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!1, A ~ B)
| snd :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!2, C ~ D)
| allc :
  Judgment .prf Γ (t, A ~ B) ->
  Judgment .prf Γ (∀c[K] t, (∀[K] A) ~ (∀[K] B))
| apptc :
  Judgment .prf Γ (t1, (∀[K] A) ~ (∀[K] B)) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c[ t2 ], (A β[C]) ~ (B β[D]))

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()
