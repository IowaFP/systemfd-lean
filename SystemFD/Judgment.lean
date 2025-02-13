import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx

inductive StableTypeMatch : Ctx Term -> Term -> Term -> Prop where
| refl :
  .some (x, _) = R.neutral_form ->
  (Γ d@ x).is_stable ->
  StableTypeMatch Γ R R
| arrow :
  StableTypeMatch (.type A::Γ) B ([S]R) ->
  StableTypeMatch Γ (A -t> B) R
| all :
  StableTypeMatch (.kind A::Γ) B ([S]R) ->
  StableTypeMatch Γ (∀[A] B) R

inductive PrefixTypeMatch : Ctx Term -> Term -> Term -> Term -> Prop where
| refl :
  .some (x, _) = B.neutral_form ->
  (Γ d@ x).is_stable ->
  PrefixTypeMatch Γ B T T
| arrow :
  PrefixTypeMatch (.type A::Γ) B V ([S]T) ->
  PrefixTypeMatch Γ (A -t> B) (A -t> V) T
| all :
  PrefixTypeMatch (.kind A::Γ) B V ([S]T) ->
  PrefixTypeMatch Γ (∀[A] B) (∀[A] V) T

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
| wfnil :  Judgment .wf [] ()
| wfempty :
  Judgment .wf Γ () ->
  Judgment .wf (.empty::Γ) ()
| wftype :
  Judgment .prf Γ (A, ★) ->
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
  Judgment .prf Γ (A, .kind) ->
  Judgment .wf Γ () ->
  Judgment .wf (.opent A::Γ) ()
| wfopenm :
  Judgment .prf Γ (A, ★) ->
  Judgment .wf Γ () ->
  Judgment .wf (.openm A::Γ) ()
| wfinsttype :
  Judgment .prf Γ (A, ★) ->
  Judgment .wf Γ () ->
  Judgment .wf (.insttype A::Γ) ()
| wfinst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t, T) ->
  Judgment .wf Γ () ->
  Judgment .wf (.inst x t::Γ) ()
| wfterm :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (t, A) ->
  Judgment .wf Γ () ->
  Judgment .wf (.term A t::Γ) ()
--------------------------------------------------------------------------------------
---- Declarations
--------------------------------------------------------------------------------------
| letdata :
  Judgment .prf Γ (T, .kind) ->
  Judgment .prf (.datatype T::Γ) (t, A) ->
  Judgment .prf Γ (.letdata T t, .decl A)
| letctor :
  Judgment .prf Γ (T, ★) ->
  valid_ctor Γ ->
  Judgment .prf (.ctor T::Γ) (t, A) ->
  Judgment .prf Γ (letctor! T t, .decl A)
| letopentype :
  Judgment .prf Γ (T, .kind) ->
  Judgment .prf (.opent T::Γ) (t, A) ->
  Judgment .prf Γ (letopentype! T t, .decl A)
| letopen :
  Judgment .prf Γ (T, ★) ->
  Judgment .prf (.openm T::Γ) (t, A) ->
  Judgment .prf Γ (letopen! T t, .decl A)
| insttype :
  Judgment .prf Γ (T, ★) ->
  Judgment .prf (.insttype T::Γ) (t, A) ->
  Judgment .prf Γ (insttype! T t, .decl A)
| inst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t1, T) ->
  Judgment .prf (.inst x t1::Γ) (t2, A) ->
  Judgment .prf Γ (.inst x t1 t2, .decl A)
| letterm :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (t, A) ->
  Judgment .prf (.term A t::Γ) (b, T) ->
  Judgment .prf Γ (.letterm A t b, .decl T)
--------------------------------------------------------------------------------------
---- Kind/Type Constructor Judgments
--------------------------------------------------------------------------------------
| ax :
  Judgment .wf Γ () ->
  Judgment .prf Γ (★, .kind)
| var :
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
  Judgment .prf Γ (A, ★) ->
  Judgment .prf (.type A::Γ) (B, ★) ->
  Judgment .prf Γ (A -t> B, ★)
| appk :
  Judgment .prf Γ (f, A -k> B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@k a, B)
| eq :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (B, ★) ->
  Judgment .prf Γ (A ~ B, ★)
--------------------------------------------------------------------------------------
---- Datatype case expressions
--------------------------------------------------------------------------------------
| ite :
  Judgment .prf Γ (p, A) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (R, ★) ->
  Judgment .prf Γ (i, B) ->
  StableTypeMatch Γ A R ->
  .some (ctorid, _) = Term.neutral_form p ->
  .some (dataid, _) = Term.neutral_form R ->
  is_datatype Γ ctorid dataid ->
  PrefixTypeMatch Γ A B T ->
  Judgment .prf Γ (T, ★) ->
  Judgment .prf Γ (e, T) ->
  Judgment .prf Γ (.ite p s i e, T)
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard :
--   .some openmid = Term.neutral_head s -> // Check that it's actually an open method?
  Judgment .prf Γ (p, A) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (R, ★) ->
  StableTypeMatch Γ A R ->
  Judgment .prf Γ (t, B) ->
  PrefixTypeMatch Γ A B T ->
  Judgment .prf Γ (T, ★) ->
  Judgment .prf Γ (.guard p s t, T)
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf (.type A::Γ) (t, B) ->
  Judgment .prf Γ (`λ[A] t, A -t> B)
| app :
  Judgment .prf Γ (f, A -t> B) ->
  Judgment .prf Γ (a, A) ->
  B' = B β[.kind] ->
  Judgment .prf Γ (f `@ a, B')
| lamt :
  Judgment .prf Γ (A, .kind) ->
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
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (refl! A, A ~ A)
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
  Judgment .prf (.empty::Γ) (t2, C ~ D) ->
  -- Could do the below instead of .empty :: Γ
  -- But like ∀c it makes sense to treat -c> as a binder
  -- even if its not binding anything
  -- C = [S]C' ->
  -- D = [S]D' ->
  Judgment .prf Γ (t1 -c> t2, (A -t> C) ~ (B -t> D))
| fst :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!1, A ~ B)
| snd :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!2, C ~ D)
| allc :
  Judgment .prf (.kind K :: Γ) (t, A ~ B) ->
  Judgment .prf Γ (∀c[K] t, (∀[K] A) ~ (∀[K] B))
| apptc :
  Judgment .prf Γ (t1, (∀[K] A) ~ (∀[K] B)) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c[ t2 ], (A β[C]) ~ (B β[D]))

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

theorem judgment_ctx_wf : Judgment v Γ idx -> ⊢ Γ := by
intro j
induction j
all_goals try simp [*]
case _ => constructor
case _ ih => constructor; apply ih
case _ j _ _ ih => constructor; apply j; apply ih
case _ j _ _ ih => constructor; apply j; apply ih
case _ j _ _ ih => constructor; apply j; apply ih
case _ j _ h _ ih => constructor; apply j; apply ih; apply h
case _ j _ _ ih => constructor; apply j; apply ih
case _ j _ _ ih => constructor; apply j; apply ih
case _ j _ _ ih => constructor; apply j; apply ih
case _ j1 j2 _ _ ih => constructor; apply j1; apply j2; apply ih
case _ j1 j2 _ _ _ ih =>  constructor; apply j1; apply j2; apply ih
case _ ih => cases ih; case _ ih _ => apply ih
