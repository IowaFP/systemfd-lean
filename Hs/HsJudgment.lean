import Hs.HsTerm
import SystemFD.Ctx
import SystemFD.Substitution
import SystemFD.Judgment

import Aesop

set_option maxHeartbeats 500000

@[aesop safe]
def HsValidHeadVariable (t : HsTerm) (test : Nat -> Bool) : Prop :=
  ∃ x, .some x = HsTerm.neutral_form t ∧ test x.fst

@[aesop safe [constructors, cases]]
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

@[aesop safe [constructors, cases]]
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

@[aesop safe [constructors, cases]]
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

@[aesop safe [constructors, cases]]
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

@[aesop safe [constructors, cases]]
inductive HsVariant where -- what i am checking
| kind | type | term | ctx

@[simp]
abbrev HsJudgmentArgs : HsVariant -> Type
| .ctx => Unit
| .kind => HsTerm × HsTerm
| .type => HsTerm × HsTerm
| .term => HsTerm × HsTerm

@[aesop safe [constructors, cases]]
inductive HsJudgment : (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Type where
-- TODO: Should I store HsCtx Γ in all the wf judgments instead of a ()
--------------------------------------------------------------------------------------
---- Well-Formed Contexts and Declarations
--------------------------------------------------------------------------------------
| wfnil :  HsJudgment .ctx [] ()
| wfempty :
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.empty::Γ) ()
| wftype :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.type A::Γ) ()
| wfkind :
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.kind A::Γ) ()
| wfdatatype :
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.datatype A::Γ) ()
| wfctor :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .ctx Γ () ->
  ValidHsCtorType Γ A ->
  HsJudgment .ctx (.ctor A::Γ) ()
| wfterm :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .term Γ (t, A) ->
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.term A t::Γ) ()

-----------------------------------
-- Implicits
-----------------------------------
| implicitArrI :
  HsJudgment .type Γ (π, `★) ->
  HsJudgment .type (.empty::Γ) (τ, `★) ->
  HsValidHeadVariable π Γ.is_opent ->
  HsJudgment .term (.type π :: Γ) (t, τ) ->
  HsJudgment .term Γ (t, π ⇒ τ) -- F a => τ
| implicitArrE :
  HsJudgment .term Γ (t, π ⇒ τ) -> -- F a => τ
  HsJudgment .term Γ (e, π) ->
  HsJudgment .term Γ (t, τ β[e])
| implicitAllI :
  HsJudgment .term (.kind A :: Γ) (t, τ) ->
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .type (.kind A :: Γ) (τ, `★) ->
  HsJudgment .term Γ (t, `∀{A} τ)
| implicitAllE :
  HsJudgment .term Γ (t, `∀{A} τ) ->
  HsJudgment .term Γ (e, A) ->
  HsJudgment .term Γ (t, τ β[e])

--------------------------------------
-- Types and Kinds
--------------------------------------
| ax :
  HsJudgment .ctx Γ () ->
  HsJudgment .kind Γ (`★, `□)
| arrowk :
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .kind Γ (B, `□) ->
  HsJudgment .kind Γ (A `-k> B, `□)
| allt :
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .type (.kind A::Γ) (B, `★) ->
  HsJudgment .type Γ (`∀{A} B, `★)
| arrow :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .type (.empty::Γ) (B, `★) ->
  HsJudgment .type Γ (A → B, `★)
| farrow :
  HsJudgment .type Γ (A, `★) ->
  HsValidHeadVariable A Γ.is_opent ->
  HsJudgment .type (.empty::Γ) (B, `★) ->
  HsJudgment .type Γ (A ⇒ B, `★)
| appk :
  HsJudgment .type Γ (f, A `-k> B) ->
  HsJudgment .type Γ (a, A) ->
  HsJudgment .type Γ (f `•k a, B)
| varTy :
  HsJudgment .ctx Γ () ->
  (Γ d@ x).is_datatype || (Γ d@ x).is_kind  ->
  .some T = (Γ d@ x).get_type ->
  HsJudgment .type Γ (`#x, T)

------------------------------------
--- Terms
------------------------------------
| var :
  HsJudgment .ctx Γ () ->
  (Γ d@ x).is_ctor || (Γ d@ x).is_term || (Γ d@ x).is_type ->
  .some T = (Γ d@ x).get_type ->
  HsJudgment .term Γ (`#x, T)
| lam :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .term (.type A :: Γ) (t, B) ->
  HsJudgment .type Γ (A → B, `★) ->
  HsJudgment .term Γ (`λ{A} t, A → B)
| app :
  HsJudgment .term Γ (t1, A → B) ->
  HsJudgment .term Γ (t2, A) ->
  B' = B β[A] ->
  HsJudgment .term Γ (t1 `• t2,  B')
| hslet :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .term Γ (t1,  A) ->
  HsJudgment .term (.term A t1 :: Γ) (t2, [S] B) ->
  HsJudgment .type Γ (B, `★) ->
  HsJudgment .term Γ (.HsLet A t1 t2,  B)
| hsIte :
  HsJudgment .term Γ (t1, A) ->
  HsJudgment .term Γ (t2, R) ->
  HsJudgment .term Γ (t3, B) ->
  HsJudgment .term Γ (t4, T) ->
  HsJudgment .type Γ (T, `★) ->
  HsJudgment .type Γ (R, `★) ->
  StableHsTypeMatch Γ A R ->
  PrefixHsTypeMatch Γ A B T ->
  HsValidHeadVariable R Γ.is_datatype ->
  HsValidHeadVariable t1 Γ.is_ctor ->
  HsJudgment .term Γ (.HsIte t1 t2 t3 t4,  T)

notation:170 Γ:170 " ⊢κ " t:170 " : " A:170 => HsJudgment HsVariant.kind Γ (t, A)
notation:170 Γ:170 " ⊢τ " t:170 " : " A:170 => HsJudgment HsVariant.type Γ (t, A)
notation:170 Γ:170 " ⊢t " t:170 " : " A:170 => HsJudgment HsVariant.term Γ (t, A)
notation:170 "⊢s " Γ:170 => HsJudgment HsVariant.ctx Γ ()

def hs_judgment_ctx_wf : (v : HsVariant) -> {idx : HsJudgmentArgs v} -> HsJudgment v Γ idx -> ⊢s Γ
| .ctx , _ , x => x
| .kind, _ , x => match x with
  | .ax h => h
  | .arrowk h _ => hs_judgment_ctx_wf .kind h
| .type , _ , x => match x with
  | .varTy h _ _ => hs_judgment_ctx_wf .ctx h
  | .appk h _ => hs_judgment_ctx_wf .type h
  | .allt h _ =>  hs_judgment_ctx_wf .kind h
  | .arrow h _ => hs_judgment_ctx_wf .type h
  | .farrow h _ _ => hs_judgment_ctx_wf .type h
| .term , _ , x => match x with
  | .implicitAllI _ h2 _ => hs_judgment_ctx_wf .kind h2
  | .implicitAllE h1 _ => hs_judgment_ctx_wf .term h1
  | .implicitArrI h1 _ _ _ => hs_judgment_ctx_wf .type h1
  | .implicitArrE h1 _ => hs_judgment_ctx_wf .term h1
  | .var h _ _ => h
  | .lam h _ _ => hs_judgment_ctx_wf .type h
  | .app h _ _ => hs_judgment_ctx_wf .term h
  | .hslet h _ _ _ => hs_judgment_ctx_wf .type h
  | .hsIte h _ _ _ _ _ _ _ _ _ => hs_judgment_ctx_wf .term h


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
 | .implicitArrI h1 h2 _ h4 => 1 + size h1 + size h2 + size h4
 | .implicitArrE h1 h2 => 1 + size h1 + size h2
 | .implicitAllI h1 h2 h3 => 1 + size h1 + size h2 + size h2
 | .implicitAllE h1 h2 => 1 + size h1 + size h2
 | .ax h1 => 1 + size h1
 | .arrowk h1 h2 => 1 + size h1 + size h2
 | .allt h1 h2 =>  1 + size h1 + size h2
 | .arrow h1 h2 => 1 + size h1 + size h2
 | .farrow h1 _ h2 => 1 + size h1 + size h2
 | .appk h1 h2 => 1 + size h1 + size h2
 | .varTy h1 _ _ => 1 + size h1
 | .var h1 _ _ => 1 + size h1
 | .lam h1 h2 h3 =>  1 + size h1 + size h2 + size h3
 | .app h1 h2 _ =>   1 + size h1 + size h2
 | .hslet h1 h2 h3 h4 =>  1 + size h1 + size h2 + size h3 + size h3
 | .hsIte h1 h2 h3 h4 h5 h6 _ _ _ _ => 1 + size h1 + size h2 + size h3 + size h4 + size h5 + size h6
end HsJudgment

instance sizeOf_HsJudgment : SizeOf (HsJudgment v Γ idx) where
  sizeOf := HsJudgment.size

@[aesop safe [constructors, cases]]
inductive HsFrameWf : Ctx HsTerm -> Frame HsTerm -> Type
| empty :
  ⊢s Γ ->
  HsFrameWf Γ .empty
| type :
  Γ ⊢τ A : `★ ->
  HsFrameWf Γ (.type A)
| kind :
  Γ ⊢κ A : `□ ->
  HsFrameWf Γ (.kind A)
| datatype :
  Γ ⊢κ A : `□ ->
  HsFrameWf Γ (.datatype A)
| ctor :
  Γ ⊢τ A : `★ ->
  ValidHsCtorType Γ A ->
  HsFrameWf Γ (.ctor A)
| term :
  Γ ⊢τ A : `★ ->
  Γ ⊢t t : A ->
  HsFrameWf Γ (.term A t)
| opent :
  Γ ⊢κ A : `□ ->
  HsFrameWf Γ (.opent A)
| openm :
  Γ ⊢τ A : `★ ->
  HsFrameWf Γ (.openm A)
-- | insttype :
--   Γ ⊢s A : `★ ->
--   ValidInstType Γ A ->
--   HsFrameWf Γ (.insttype A)
-- | inst :
--   .openm T = Γ d@ x ->
--   Γ ⊢s t : T ->
--   HsFrameWf Γ (.inst #x t)

notation:170 Γ:170 " ⊢s " f:170 => HsFrameWf Γ f
