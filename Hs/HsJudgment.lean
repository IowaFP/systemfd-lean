import Hs.HsTerm
import SystemFD.Ctx
import SystemFD.Substitution
import SystemFD.Judgment

set_option maxHeartbeats 500000

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
  HsJudgment .prf (.empty::Γ) (τ, `★) ->
  HsValidHeadVariable π Γ.is_opent ->
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
  HsJudgment .prf (.kind A :: Γ) (τ, `★) ->
  HsJudgment .prf Γ (t, `∀{A} τ)
| implicitAllE :
  HsJudgment .prf Γ (t, `∀{A} τ) ->
  HsJudgment .prf Γ (e, A) ->
  HsJudgment .prf Γ (t, τ β[e])

--------------------------------------
-- Types and Kinds
--------------------------------------
| ax :
  HsJudgment .wf Γ () ->
  HsJudgment .prf Γ (`★, `□)
| arrowk :
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .prf Γ (B, `□) ->
  HsJudgment .prf Γ (A `-k> B, `□)
| allt :
  HsJudgment .prf Γ (A, `□) ->
  HsJudgment .prf (.kind A::Γ) (B, `★) ->
  HsJudgment .prf Γ (`∀{A} B, `★)
| arrow :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .prf (.empty::Γ) (B, `★) ->
  HsJudgment .prf Γ (A → B, `★)
| farrow :
  HsJudgment .prf Γ (A, `★) ->
  HsValidHeadVariable A Γ.is_opent ->
  HsJudgment .prf (.empty::Γ) (B, `★) ->
  HsJudgment .prf Γ (A ⇒ B, `★)
| appk :
  HsJudgment .prf Γ (f, A `-k> B) ->
  HsJudgment .prf Γ (a, A) ->
  HsJudgment .prf Γ (f `•k a, B)

------------------------------------
--- Terms
------------------------------------
| var :
  HsJudgment .wf Γ () ->
  .some T = (Γ d@ x).get_type ->
  HsJudgment .prf Γ (`#x, T)
| lam :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .prf (.type A :: Γ) (t, B) ->
  HsJudgment .prf Γ (A → B, `★) ->
  HsJudgment .prf Γ (`λ{A} t, A → B)
| app :
  HsJudgment .prf Γ (t1, A → B) ->
  HsJudgment .prf Γ (t2, A) ->
  B' = B β[A] ->
  HsJudgment .prf Γ (t1 `• t2,  B')
| hslet :
  HsJudgment .prf Γ (A, `★) ->
  HsJudgment .prf Γ (t1,  A) ->
  HsJudgment .prf (.term A t1 :: Γ) (t2, [S] B) ->
  HsJudgment .prf Γ (B, `★) ->
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

def hs_judgment_ctx_wf : (v : JudgmentVariant) -> {idx : HsJudgmentArgs v} -> HsJudgment v Γ idx -> ⊢s Γ
| .wf , _ , x => x
| .prf , _ , x => match x with
  | .implicitAllI _ h2 _ => hs_judgment_ctx_wf .prf h2
  | .implicitAllE h1 _ => hs_judgment_ctx_wf .prf h1
  | .implicitArrI h1 _ _ _ _ => hs_judgment_ctx_wf .prf h1
  | .implicitArrE h1 _ => hs_judgment_ctx_wf .prf h1
  | .ax h => h
  | .arrowk h _ => hs_judgment_ctx_wf .prf h
  | .appk h _ => hs_judgment_ctx_wf .prf h
  | .allt h _ =>  hs_judgment_ctx_wf .prf h
  | .arrow h _  => hs_judgment_ctx_wf .prf h
  | .farrow h _ _ => hs_judgment_ctx_wf .prf h
  | .var h _ => h
  | .lam h _ _ => hs_judgment_ctx_wf .prf h
  | .app h _ _ => hs_judgment_ctx_wf .prf h
  | .hslet h _ _ _ => hs_judgment_ctx_wf .prf h
  | .hsIte h _ _ _ _ _ _ _ _ _ => hs_judgment_ctx_wf .prf h


namespace HsJudgment
 @[simp]
 def size : HsJudgment v Γ idx -> Nat
 | .wfnil => 0
 | .wfempty h => 1 + size h
 | .wftype h1 h2 => 1 + size h1 + size h2
 | .wfkind h1 h2 => 1 + size h1 + size h2
 | .wfdatatype h1 h2 => 1 + size h1 + size h2
 | .wfctor h1 h2 _ => 1 + size h1 + size h2
 | .wfterm h1 h2 h3 => 1 + size h1 + size h2 + size h3
 | .implicitArrI h1 h2 _ h3 h4 => 1 + size h1 + size h2 + size h3  + size h4
 | .implicitArrE h1 h2 => 1 + size h1 + size h2
 | .implicitAllI h1 h2 h3 => 1 + size h1 + size h2 + size h2
 | .implicitAllE h1 h2 => 1 + size h1 + size h2
 | .ax h1 => 1 + size h1
 | .arrowk h1 h2 => 1 + size h1 + size h2
 | .allt h1 h2 =>  1 + size h1 + size h2
 | .arrow h1 h2 => 1 + size h1 + size h2
 | .farrow h1 _ h2 => 1 + size h1 + size h2
 | .appk h1 h2 => 1 + size h1 + size h2
 | .var h1 _ => 1 + size h1
 | .lam h1 h2 h3 =>  1 + size h1 + size h2 + size h3
 | .app h1 h2 _ =>   1 + size h1 + size h2
 | .hslet h1 h2 h3 h4 =>  1 + size h1 + size h2 + size h3 + size h3
 | .hsIte h1 h2 h3 h4 h5 h6 _ _ _ _ => 1 + size h1 + size h2 + size h3 + size h4 + size h5 + size h6
end HsJudgment

instance sizeOf_HsJudgment : SizeOf (HsJudgment v Γ idx) where
  sizeOf := HsJudgment.size


inductive HsFrameWf : Ctx HsTerm -> Frame HsTerm -> Type
| empty :
  ⊢s Γ ->
  HsFrameWf Γ .empty
| type :
  Γ ⊢s A : `★ ->
  HsFrameWf Γ (.type A)
| kind :
  Γ ⊢s A : `□ ->
  HsFrameWf Γ (.kind A)
| datatype :
  Γ ⊢s A : `□ ->
  HsFrameWf Γ (.datatype A)
| ctor :
  Γ ⊢s A : `★ ->
  ValidHsCtorType Γ A ->
  HsFrameWf Γ (.ctor A)
| term :
  Γ ⊢s A : `★ ->
  Γ ⊢s t : A ->
  HsFrameWf Γ (.term A t)

-- | opent :
--   Γ ⊢s A : `□ ->
--   HsFrameWf Γ (.opent A)
-- | openm :
--   Γ ⊢s A : `★ ->
--   HsFrameWf Γ (.openm A)
-- | insttype :
--   Γ ⊢s A : `★ ->
--   ValidInstType Γ A ->
--   HsFrameWf Γ (.insttype A)
-- | inst :
--   .openm T = Γ d@ x ->
--   Γ ⊢s t : T ->
--   HsFrameWf Γ (.inst #x t)

notation:170 Γ:170 " ⊢s " f:170 => HsFrameWf Γ f
