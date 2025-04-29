import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx

def ValidHeadVariable (t : Term) (test : Nat -> Bool) : Prop :=
  ∃ x, .some x = Term.neutral_form t ∧ test x.fst

inductive ValidCtorType : Ctx Term -> Term -> Prop where
| refl :
  ValidHeadVariable R Γ.is_datatype ->
  ValidCtorType Γ R
| arrow :
  ValidCtorType (.empty::Γ) B ->
  ValidCtorType Γ (A -t> B)
| all :
  ValidCtorType (.kind A::Γ) B ->
  ValidCtorType Γ (∀[A] B)


inductive ValidInstType : Ctx Term -> Term -> Prop where
| refl :
  ValidHeadVariable R Γ.is_opent ->
  ValidInstType Γ R
| arrow :
  ValidInstType (.empty::Γ) B ->
  ValidInstType Γ (A -t> B)
| all :
  ValidInstType (.kind A::Γ) B ->
  ValidInstType Γ (∀[A] B)

inductive StableTypeMatch : Ctx Term -> Term -> Term -> Prop where
| refl :
  ValidHeadVariable R Γ.is_stable ->
  StableTypeMatch Γ R R
| arrow :
  ValidHeadVariable R (Ctx.is_stable Γ) ->
  StableTypeMatch (.empty::Γ) B ([S]R) ->
  StableTypeMatch Γ (A -t> B) R
| all :
  ValidHeadVariable R (Ctx.is_stable Γ) ->
  StableTypeMatch (.kind A::Γ) B ([S]R) ->
  StableTypeMatch Γ (∀[A] B) R

inductive PrefixTypeMatch : Ctx Term -> Term -> Term -> Term -> Prop where
| refl :
  ValidHeadVariable B Γ.is_stable ->
  PrefixTypeMatch Γ B T T
| arrow :
  PrefixTypeMatch (.empty::Γ) B V ([S]T) ->
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
---- Well-Formed Contexts and Declarations
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
  ValidCtorType Γ A ->
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
  ValidInstType Γ A ->
  Judgment .wf (.insttype A::Γ) ()
| wfinst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t, T) ->
  Judgment .wf Γ () ->
  Judgment .wf (.inst #x t::Γ) ()
| wfterm :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (t, A) ->
  Judgment .wf Γ () ->
  Judgment .wf (.term A t::Γ) ()
--------------------------------------------------------------------------------------
---- Local Let Binding
--------------------------------------------------------------------------------------
| letterm :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (t, A) ->
  Judgment .prf (.term A t::Γ) (b, [S]T) ->
  Judgment .prf Γ (T, ★) ->
  Judgment .prf Γ (.letterm A t b, T)
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
  Judgment .prf (.kind A::Γ) (B, ★) ->
  Judgment .prf Γ (∀[A] B, ★)
| arrow :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf (.empty::Γ) (B, ★) ->
  Judgment .prf Γ (A -t> B, ★)
| appk :
  Judgment .prf Γ (f, A -k> B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@k a, B)
| eq :
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (B, K) ->
  Judgment .prf Γ (A ~ B, ★)
--------------------------------------------------------------------------------------
---- Datatype case expressions
--------------------------------------------------------------------------------------
| ite :
  Judgment .prf Γ (p, A) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (R, ★) ->
  Judgment .prf Γ (i, B) ->
  ValidHeadVariable p Γ.is_ctor ->
  ValidHeadVariable R Γ.is_datatype ->
  StableTypeMatch Γ A R ->
  PrefixTypeMatch Γ A B T ->
  Judgment .prf Γ (T, ★) ->
  Judgment .prf Γ (e, T) ->
  Judgment .prf Γ (.ite p s i e, T)
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard :
  Judgment .prf Γ (p, A) ->
  Judgment .prf Γ (s, R) ->
  Judgment .prf Γ (R, ★) ->
  Judgment .prf Γ (t, B) ->
  ValidHeadVariable p Γ.is_insttype ->
  ValidHeadVariable R Γ.is_opent ->
  StableTypeMatch Γ A R ->
  PrefixTypeMatch Γ A B T ->
  Judgment .prf Γ (T, ★) ->
  Judgment .prf Γ (.guard p s t, T)
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf (.type A::Γ) (t, B) ->
  Judgment .prf Γ (A -t> B, ★) ->
  Judgment .prf Γ (`λ[A] t, A -t> B)
| app :
  Judgment .prf Γ (f, A -t> B) ->
  Judgment .prf Γ (a, A) ->
  B' = B β[a] ->
  Judgment .prf Γ (f `@ a, B')
| lamt :
  Judgment .prf Γ (A, .kind) ->
  Judgment .prf (.kind A::Γ) (t, B) ->
  Judgment .prf Γ (∀[A] B, ★) ->
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
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (refl! A, A ~ A)
| sym :
  Judgment .prf Γ (t, A ~ B) ->
  Judgment .prf Γ (sym! t, B ~ A)
| seq :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, B ~ C) ->
  Judgment .prf Γ (t1 `; t2, A ~ C)
| appc :
  Judgment .prf Γ (A, K1 -k> K2) ->
  Judgment .prf Γ (B, K1 -k> K2) ->
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (C, K1) ->
  Judgment .prf Γ (D, K1) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c t2, (A `@k C) ~ (B `@k D))
| arrowc :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (B, ★) ->
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf (.empty::Γ) (C, ★) ->
  Judgment .prf (.empty::Γ) (D, ★) ->
  Judgment .prf (.empty::Γ) (t2, C ~ D) ->
  Judgment .prf Γ (t1 -c> t2, (A -t> C) ~ (B -t> D))
| fst :
  Judgment .prf Γ (A, K1 -k> K2) ->
  Judgment .prf Γ (B, K1 -k> K2) ->
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!1, A ~ B)
| snd :
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (C, K) ->
  Judgment .prf Γ (D, K) ->
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (t.!2, C ~ D)
| allc :
  Judgment .prf Γ (∀[K] A, ★) ->
  Judgment .prf Γ (∀[K] B, ★) ->
  Judgment .prf (.kind K :: Γ) (t, A ~ B) ->
  Judgment .prf Γ (∀c[K] t, (∀[K] A) ~ (∀[K] B))
| apptc :
  Judgment .prf Γ (t1, (∀[K] A) ~ (∀[K] B)) ->
  Judgment .prf Γ (C, K) ->
  Judgment .prf Γ (D, K) ->
  Judgment .prf Γ (t2, C ~ D) ->
  A' = A β[C] ->
  B' = B β[D] ->
  Judgment .prf Γ (t1 `@c[ t2 ], A' ~ B')

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
case _ j1 _ j2 _ ih => constructor; apply j1; apply ih; apply j2
case _ j1 j2 _ _ ih => constructor; apply j1; apply j2; apply ih
case _ j1 j2 _ _ _ ih =>  constructor; apply j1; apply j2; apply ih

inductive FrameWf : Ctx Term -> Frame Term -> Prop
| empty :
  ⊢ Γ ->
  FrameWf Γ .empty
| type :
  Γ ⊢ A : ★ ->
  FrameWf Γ (.type A)
| kind :
  Γ ⊢ A : .kind ->
  FrameWf Γ (.kind A)
| datatype :
  Γ ⊢ A : .kind ->
  FrameWf Γ (.datatype A)
| ctor :
  Γ ⊢ A : ★ ->
  ValidCtorType Γ A ->
  FrameWf Γ (.ctor A)
| opent :
  Γ ⊢ A : .kind ->
  FrameWf Γ (.opent A)
| openm :
  Γ ⊢ A : ★ ->
  FrameWf Γ (.openm A)
| insttype :
  Γ ⊢ A : ★ ->
  ValidInstType Γ A ->
  FrameWf Γ (.insttype A)
| inst :
  .openm T = Γ d@ x ->
  Γ ⊢ t : T ->
  FrameWf Γ (.inst #x t)
| term :
  Γ ⊢ A : ★ ->
  Γ ⊢ t : A ->
  FrameWf Γ (.term A t)

notation:170 Γ:170 " ⊢ " f:170 => FrameWf Γ f

inductive SpineType : Ctx Term -> Term -> Term -> Prop where
| refl :
  SpineType Γ T T
| arrow :
  Γ ⊢ a : A' ->
  Γ ⊢ (A -t> B) : ★ ->
  SpineType Γ (B β[a]) T ->
  SpineType Γ (A -t> B) T
| all :
  Γ ⊢ a : A ->
  Γ ⊢ (∀[A] B) : ★ ->
  SpineType Γ (B β[a]) T ->
  SpineType Γ (∀[A] B) T
| arrowk :
  Γ ⊢ (A -k> B) : .kind ->
  SpineType Γ B T ->
  SpineType Γ (A -k> B) T

inductive ListJudgment : Ctx Term -> List Term -> Term -> Prop where
| nil : ListJudgment Γ [] A
| cons :
  Γ ⊢ h : A ->
  ListJudgment Γ tl A ->
  ListJudgment Γ (h :: tl) A
