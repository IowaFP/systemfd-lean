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

-- def TyCtx := List (Frame HsTerm)
-- def TmCtx := List (Frame HsTerm)


-- @[simp]
-- abbrev HsCtxArgs : HsVariant -> Type
-- | .ctx => Unit
-- | .kind => Unit
-- | .type => TyCtx
-- | .term => TyCtx × TmCtx

@[aesop safe [constructors, cases]]
inductive HsJudgment : (v : HsVariant) -> Ctx HsTerm -> Ctx HsTerm -> HsJudgmentArgs v -> Type where
-- TODO: Should I store HsCtx Γ in all the wf judgments instead of a ()
--------------------------------------------------------------------------------------
---- Well-Formed Contexts and Declarations
--------------------------------------------------------------------------------------
| wfnil :  HsJudgment .ctx [] [] ()
| wfempty :
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.empty::Γ1) (.empty::Γ2) ()
| wftype :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.type A::Γ1) (.type A::Γ2) ()
| wfkind :
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.kind A::Γ) (.kind A::Γ) ()
| wfdatatype :
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.datatype A::Γ1) (.datatype A::Γ2) ()
| wfctor :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  ValidHsCtorType Γ2 A ->
  HsJudgment .ctx (.ctor A::Γ1) (.ctor A::Γ2) ()
| wfterm :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .term Γ1 Γ2 (t, A) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.term A t::Γ1) (.term A t::Γ2) ()
| wfopenm :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.openm A::Γ1) (.openm A::Γ2) ()
| wfImpType :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.type A :: Γ1) Γ2 ()
| wfImpKind :
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .ctx (.type A :: Γ1) Γ2 ()
-----------------------------------
-- Implicits
-----------------------------------
| implicitArrI :
  HsJudgment .type Γ1 Γ2 (π, `★) ->
  HsJudgment .type (.empty::Γ1) (.empty::Γ2) (τ, `★) ->
  HsValidHeadVariable π Γ1.is_opent ->
  HsJudgment .term (.type π :: Γ1) (.type π :: Γ2) (t, τ) ->
  HsJudgment .ctx (.type π :: Γ1) Γ2  () ->
  HsJudgment .term (.type π :: Γ1) Γ2 (t, π ⇒ τ) -- F a => τ
| implicitArrE :
  HsJudgment .term Γ1 Γ2 (t, π ⇒ τ) -> -- F a => τ
  HsJudgment .term Γ1 Γ2 (e, π) ->
  τ' = τ β[e] ->
  HsJudgment .type Γ1 Γ2 (τ', `★) ->
  HsJudgment .term Γ1 Γ2 (t, τ')
| implicitAllI :
  HsJudgment .term (.kind A :: Γ) (.kind A :: Γ) (t, τ) ->
  HsJudgment .kind Γ Γ (A, `□) ->
  -- HsJudgment .ctx (.kind A :: Γ) Γ  () ->
  HsJudgment .term (.kind A :: Γ) Γ (t, `∀{A} τ)
| implicitAllE :
  HsJudgment .type Γ1 Γ2 (`∀{A} τ, `★) ->
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .term Γ1 Γ2 (t, `∀{A} τ) ->
  HsJudgment .type Γ1 Γ2 (e, A) ->
  τ' = τ β[e] ->
  HsJudgment .term Γ1 Γ2 (t, τ')

--------------------------------------
-- Types and Kinds
--------------------------------------
| ax :
  HsJudgment .ctx Γ1 Γ2 () ->
  HsJudgment .kind Γ1 Γ2 (`★, `□)
| arrowk :
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .kind Γ1 Γ2 (B, `□) ->
  HsJudgment .kind Γ1 Γ2 (A `-k> B, `□)
| allt :
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .type (.kind A::Γ1) (.kind A::Γ2) (B, `★) ->
  HsJudgment .type Γ1 Γ2 (`∀{A} B, `★)
| arrow :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .type (.empty::Γ1) (.empty::Γ2) (B, `★) ->
  HsJudgment .type Γ1 Γ2 (A → B, `★)
| farrow :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsValidHeadVariable A Γ1.is_opent ->
  HsJudgment .type (.empty::Γ1) (.empty::Γ2) (B, `★) ->
  HsJudgment .type Γ1 Γ2 (A ⇒ B, `★)
| appk :
  HsJudgment .type Γ1 Γ2 (f, A `-k> B) ->
  HsJudgment .type Γ1 Γ2 (a, A) ->
  HsJudgment .kind Γ1 Γ2 (A, `□) ->
  HsJudgment .kind Γ1 Γ2 (B, `□) ->
  HsJudgment .type Γ1 Γ2 (f `•k a, B)
| varTy :
  HsJudgment .ctx Γ1 Γ2 () ->
  (Γ1 d@ x).is_datatype || (Γ1 d@ x).is_kind  ->
  .some T = (Γ1 d@ x).get_type ->
  HsJudgment .kind Γ1 Γ2 (T, `□) ->
  HsJudgment .type Γ1 Γ2 (`#x, T)

------------------------------------
--- Terms
------------------------------------
| var :
  HsJudgment .ctx Γ Γ () ->
  (Γ d@ x).is_ctor || (Γ d@ x).is_term || (Γ d@ x).is_type ->
  .some T = (Γ d@ x).get_type ->
  HsJudgment .term Γ Γ (`#x, T)
| lam :
  HsJudgment .type Γ Γ (A, `★) ->
  HsJudgment .term (.type A :: Γ) (.type A :: Γ) (t, B) ->
  HsJudgment .type (.empty :: Γ) (.empty :: Γ) (B, `★) ->
  HsJudgment .term Γ Γ (`λ{A} t, A → B)
| app :
  HsJudgment .term Γ Γ (t1, A → B) ->
  HsJudgment .term Γ Γ (t2, A) ->
  B' = B β[t2] ->
  HsJudgment .type Γ Γ (A, `★) ->
  HsJudgment .type Γ Γ (B', `★) ->
  HsJudgment .term Γ Γ (t1 `• t2,  B')
| hslet :
  HsJudgment .type Γ Γ (A, `★) ->
  HsJudgment .term Γ Γ (t1,  A) ->
  B' = [S]B ->
  HsJudgment .term (.term A t1 :: Γ) (.term A t1 :: Γ) (t2, B') ->
  HsJudgment .type Γ Γ (B, `★) ->
  HsJudgment .term Γ Γ (.HsLet A t1 t2,  B)
| hsIte :
  HsJudgment .type Γ1 Γ2 (A, `★) ->
  HsJudgment .type Γ1 Γ2 (R, `★) ->
  HsJudgment .type Γ1 Γ2 (B, `★) ->
  HsJudgment .type Γ1 Γ2 (T, `★) ->
  HsJudgment .term Γ1 Γ2 (t1, A) ->
  HsJudgment .term Γ1 Γ2 (t2, R) ->
  HsJudgment .term Γ1 Γ2 (t3, B) ->
  HsJudgment .term Γ1 Γ2 (t4, T) ->
  StableHsTypeMatch Γ1 A R ->
  PrefixHsTypeMatch Γ1 A B T ->
  HsValidHeadVariable R Γ1.is_datatype ->
  HsValidHeadVariable t1 Γ1.is_ctor ->
  HsJudgment .term Γ1 Γ2 (.HsIte t1 t2 t3 t4,  T)

notation:170 Γ1:170 " ;; " Γ2:170 " ⊢κ " t:170 " : " A:170 => HsJudgment HsVariant.kind Γ1 Γ2 (t, A)
notation:170 Γ1:170 " ;; " Γ2:170 " ⊢τ " t:170 " : " A:170 => HsJudgment HsVariant.type Γ1 Γ2 (t, A)
notation:170 Γ1:170 " ;; " Γ2:170 " ⊢t " t:170 " : " A:170 => HsJudgment HsVariant.term Γ1 Γ2 (t, A)
notation:170 "⊢s[ " Γ1 " ◆ " Γ2 " ]"=> HsJudgment HsVariant.ctx Γ1 Γ2 ()
notation:170 "⊢s " Γ => HsJudgment HsVariant.ctx Γ Γ ()

def wf_ctx :  HsJudgment .ctx Γ1 Γ2 h -> ⊢s[ Γ1 ◆ Γ2 ] :=
λ x => x

def hs_judgment_ctx_wf : (v : HsVariant) -> {idx : HsJudgmentArgs v} -> (HsJudgment v Γ1 Γ2 idx) -> ⊢s[ Γ1 ◆ Γ2 ]
| .ctx , _ , x => x
| .kind, _ , x => match x with
  | .ax h => h
  | .arrowk h _ => hs_judgment_ctx_wf .kind h
| .type , _ , x => match x with
  | .varTy h _ _ _ => hs_judgment_ctx_wf .ctx h
  | .appk _ _ h _ => hs_judgment_ctx_wf .kind h
  | .allt h _ =>  hs_judgment_ctx_wf .kind h
  | .arrow h _ => hs_judgment_ctx_wf .type h
  | .farrow h _ _ => hs_judgment_ctx_wf .type h
| .term , _ , x => match x with
  | .implicitAllI _ h  => hs_judgment_ctx_wf .kind h
  | .implicitAllE h1 _ _ _ _ => hs_judgment_ctx_wf .type h1
  | .implicitArrI _ _ _ _ h => h
  | .implicitArrE h1 _ _ _ => hs_judgment_ctx_wf .term h1
  | .var h _ _ => h
  | .lam h _ _ => hs_judgment_ctx_wf .type h
  | .app h _ _ _ _ => hs_judgment_ctx_wf .term h
  | .hslet h _ _ _ _ => hs_judgment_ctx_wf .type h
  | .hsIte h _ _ _ _ _ _ _ _ _ _ _ => hs_judgment_ctx_wf .type h


namespace HsJudgment
 @[simp]
 def size : HsJudgment v Γ1 Γ2 idx -> Nat
 | .wfnil => 0
 | .wfempty h => 1 + size h
 | .wftype h1 h2 => 1 + size h1 + size h2
 | .wfkind h1 h2 => 1 + size h1 + size h2
 | .wfdatatype h1 h2 => 1 + size h1 + size h2
 | .wfctor h1 h2 _ => 1 + size h1 + size h2
 | .wfopenm h1 h2 => 1 + size h1 + size h2
 | .wfterm h1 h2 h3 => 1 + size h1 + size h2 + size h3
 | .wfImpType h1 h2 => 1 + size h1 + size h2
 | .wfImpKind h1 h2 => 1 + size h1 + size h2
 | .implicitArrI h1 h2 _ h4 h5 => 1 + size h1 + size h2 + size h4 + size h5
 | .implicitArrE h1 h2 _ h3 => 1 + size h1 + size h2 + size h3
 | .implicitAllI h1 h2 h3 => 1 + size h1 + size h2 + size h3
 | .implicitAllE h1 h2 h3 h4 _ => 1 + size h1 + size h2 + size h3 + size h4
 | .ax h1 => 1 + size h1
 | .arrowk h1 h2 => 1 + size h1 + size h2
 | .allt h1 h2 =>  1 + size h1 + size h2
 | .arrow h1 h2 => 1 + size h1 + size h2
 | .farrow h1 _ h2 => 1 + size h1 + size h2
 | .appk h1 h2 h3 h4 => 1 + size h1 + size h2 + size h3 + size h4
 | .varTy h1 _ _ h2 => 1 + size h1 + size h2
 | .var h1 _ _ => 1 + size h1
 | .lam h1 h2 h3 =>  1 + size h1 + size h2 + size h3
 | .app h1 h2 _ h3 h4 =>   1 + size h1 + size h2 + size h3 + size h4
 | .hslet h1 h2 _ h3 h4 =>  1 + size h1 + size h2 + size h3 + size h4
 | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ =>
   1 + size h1 + size h2 + size h3 + size h4 + size h5 + size h6 + size h7 + size h8
end HsJudgment

instance sizeOf_HsJudgment : SizeOf (HsJudgment v Γ1 Γ2 idx) where
  sizeOf := HsJudgment.size

@[aesop safe [constructors, cases]]
inductive HsFrameWf : Ctx HsTerm -> Ctx HsTerm -> Frame HsTerm -> Type
| empty :
  ⊢s[ Γ ◆ Γ] ->
  HsFrameWf Γ Γ .empty
| type :
  (Γ ;; Γ ⊢τ A : `★) ->
  HsFrameWf Γ Γ (.type A)
| kind :
  Γ ;; Γ ⊢κ A : `□ ->
  HsFrameWf Γ Γ (.kind A)
| datatype :
  Γ ;; Γ ⊢κ A : `□ ->
  HsFrameWf Γ Γ (.datatype A)
| ctor :
  Γ ;; Γ ⊢τ A : `★ ->
  ValidHsCtorType Γ A ->
  HsFrameWf Γ Γ (.ctor A)
| term :
  Γ ;; Γ  ⊢τ A : `★ ->
  Γ ;; Γ ⊢t t : A ->
  HsFrameWf Γ Γ (.term A t)
| opent :
  Γ ;; Γ ⊢κ A : `□ ->
  HsFrameWf Γ Γ (.opent A)
| openm :
  Γ ;; Γ ⊢τ A : `★ ->
  HsFrameWf Γ Γ (.openm A)

notation:170 Γ1:170 ";;" Γ2:170 " ⊢s " f:170 => HsFrameWf Γ1 Γ2 f
