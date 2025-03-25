import Hs.HsTerm
import SystemFD.Ctx
import SystemFD.Substitution
import SystemFD.Judgment

def HsValidHeadVariable (t : HsTerm) (test : Nat -> Bool) : Prop :=
  ∃ x, .some x = HsTerm.neutral_form t ∧ test x.fst

inductive ValidHsCtorType : Ctx HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_datatype ->
  ValidHsCtorType Γ R
| arrow :
  ValidHsCtorType (.empty::Γ) B ->
  ValidHsCtorType Γ (A → B)
| farrow :
  ValidHsCtorType (.empty::Γ) B ->
  ValidHsCtorType Γ (A ⇒ B)
| all :
  ValidHsCtorType (.kind A::Γ) B ->
  ValidHsCtorType Γ (`∀{A} B)


inductive ValidHsInstType : Ctx HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_opent ->
  ValidHsInstType Γ R
| arrow :
  ValidHsInstType (.empty::Γ) B ->
  ValidHsInstType Γ (A → B)
| farrow :
  ValidHsInstType (.empty::Γ) B ->
  ValidHsInstType Γ (A ⇒ B)
| all :
  ValidHsInstType (.kind A::Γ) B ->
  ValidHsInstType Γ (`∀{A} B)

inductive StableHsTypeMatch : Ctx HsTerm -> HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_stable ->
  StableHsTypeMatch Γ R R
| arrow :
  HsValidHeadVariable R (Ctx.is_stable Γ) ->
  StableHsTypeMatch (.empty::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (A → B) R
| farrow :
  HsValidHeadVariable R (Ctx.is_stable Γ) ->
  StableHsTypeMatch (.empty::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (A ⇒ B) R
| all :
  HsValidHeadVariable R (Ctx.is_stable Γ) ->
  StableHsTypeMatch (.kind A::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (`∀{A} B) R

inductive PrefixHsTypeMatch : Ctx HsTerm -> HsTerm -> HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable B Γ.is_stable ->
  PrefixHsTypeMatch Γ B T T
| arrow :
  PrefixHsTypeMatch (.empty::Γ) B V ([S]T) ->
  PrefixHsTypeMatch Γ (A → B) (A → V) T
| all :
  PrefixHsTypeMatch (.kind A::Γ) B V ([S]T) ->
  PrefixHsTypeMatch Γ (`∀{A} B) (`∀{A} V) T


@[simp]
abbrev HsJudgmentArgs : JudgmentVariant -> Type
| JudgmentVariant.wf => Unit
| JudgmentVariant.prf => HsTerm × HsTerm


inductive HsJudgment : (v : JudgmentVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Type where
--------------------------------------------------------------------------------------
---- Well-Formed Contexts and Declarations
--------------------------------------------------------------------------------------
| wfnil :  HsJudgment .wf [] ()
| wfempty :
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.empty::Γ) ()
| wftype :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.type A::Γ) ()
| wfkind :
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.kind A::Γ) ()
| wfdatatype :
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.datatype A::Γ) ()
| wfctor :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .wf Γ () ->
  ValidHsCtorType Γ A ->
  HsJudgment .wf (.ctor A::Γ) ()
| wfopent :
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.opent A::Γ) ()
| wfopenm :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.openm A::Γ) ()
| wfinsttype :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .wf Γ () ->
  ValidHsInstType Γ A ->
  HsJudgment .wf (.insttype A::Γ) ()
| wfinst :
  .openm T = Γ d@ x ->
  HsJudgment .prf Γ (t, T) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.inst `#x t::Γ) ()
| wfterm :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .prf Γ (t, A) ->
  HsJudgment .wf Γ () ->
  HsJudgment .wf (.term A t::Γ) ()

-----------------------------------
-- Implicits
-----------------------------------
| implicitArrI :
  HsJudgment .prf Γ (π, `★) ->
  HsJudgment .prf (.empty :: Γ) (t, τ) ->
  HsJudgment .prf Γ (e, π) ->
  HsJudgment .prf Γ (t, π ⇒ τ) -- F a => τ
| implicitArrE :
  HsJudgment .prf Γ (t, π ⇒ τ) -> -- F a => τ
  HsJudgment .prf Γ (e, π) ->
  HsJudgment .prf Γ (t, τ β[e])
| implicitAllI :
  HsJudgment .prf (.kind A :: Γ) (t, τ) ->
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .prf Γ (t, `∀{A} τ)
| implicitAllE :
  HsJudgment .prf Γ (t, `∀{A} τ) ->
  HsJudgment .prf Γ (e, A) ->
  HsJudgment .prf Γ (t, τ β[e])

------------------------------------
--- Terms
------------------------------------
| var :
  HsJudgment .prf Γ (T, `★) ->
  (Γ d@ x).get_type = .some T ->
  HsJudgment .prf Γ (`#x, T)
| lam :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .prf Γ (A → B, `★) ->
  HsJudgment .prf (.type A :: Γ) (t, B) ->
  HsJudgment .prf Γ (`λ{A} t, A → B)
| app :
  HsJudgment .prf Γ (t1, A → B) ->
  HsJudgment .prf Γ (t2, A) ->
  B' = B β[A] ->
  HsJudgment .prf Γ (t1 `• t2,  B')
| hslet :
  HsJudgment .prf Γ (t1,  A) ->
  HsJudgment .prf (.term A t1 :: Γ) (t2, [S] B) ->
  HsJudgment .prf Γ (.HsLet A t1 t2,  B)
| hsIte :
  HsJudgment .prf Γ (t1, A) ->
  HsJudgment .prf Γ (t2, R) ->
  HsJudgment .prf Γ (t3, B) ->
  HsJudgment .prf Γ (t4, T) ->
  HsJudgment .prf Γ (T, `★) ->
  HsJudgment .prf Γ (R, `★) ->
  StableHsTypeMatch Γ A R ->
  PrefixHsTypeMatch Γ A B T ->
  HsValidHeadVariable R Γ.is_datatype ->
  HsValidHeadVariable t1 Γ.is_ctor ->
  HsJudgment .prf Γ (.HsIte t1 t2 t3 t4,  T)

notation:170 Γ:170 " ⊢s " t:170 " : " A:170 => HsJudgment JudgmentVariant.prf Γ (t, A)
notation:170 "⊢s " Γ:170 => HsJudgment JudgmentVariant.wf Γ ()


-- theorem hsJ_preserves_kinds : Γ ⊢s t : τ -> Γ ⊢s τ : ★ := by
-- intro j; induction j;
-- case _ => assumption
-- case _ => apply Judgment.arrow; assumption; assumption
-- case implicitArrE e h1 h2 h3 =>
--   cases h3; case _ h3 =>
--   have lem := beta_empty e h3; simp at lem; assumption;
-- case implicitAllI h1 h2 =>
--   apply Judgment.allt; assumption; assumption
-- case implicitAllE h1 h2 =>
--   cases h2; case _ h =>
--   have lem := beta_kind h h1; simp at lem; assumption;
-- case _ => assumption
-- case _ A _ _ _ _ _ h1 h2 h3 =>
--   cases h2; case _ h2 =>
--   have lem := beta_empty A h2; simp at lem; rw [h1]; assumption
-- case letterm j1 j2 h1 h2 =>
--   sorry
-- case _ h => assumption
