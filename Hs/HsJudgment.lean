import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Substitution

-- import Aesop

set_option maxHeartbeats 500000

-- @[aesop safe]
def HsValidHeadVariable (t : HsTerm) (test : Nat -> Bool) : Prop :=
  ∃ x, .some x = HsTerm.neutral_form t ∧ test x.fst

-- @[aesop safe [constructors, cases]]
inductive ValidHsCtorType : HsCtx HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_datatypeDecl ->
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

-- @[aesop safe [constructors, cases]]
inductive ValidHsInstType : HsCtx HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_classDecl ->
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

-- @[aesop safe [constructors, cases]]
inductive StableHsTypeMatch : HsCtx HsTerm -> HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable R Γ.is_stable ->
  StableHsTypeMatch Γ R R
| arrow :
  HsValidHeadVariable R (HsCtx.is_stable Γ) ->
  StableHsTypeMatch (.empty::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (A → B) R
| farrow :
  HsValidHeadVariable R (HsCtx.is_stable Γ) ->
  StableHsTypeMatch (.empty::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (A ⇒ B) R
| all :
  HsValidHeadVariable R (HsCtx.is_stable Γ) ->
  StableHsTypeMatch (.kind A::Γ) B ([S]R) ->
  StableHsTypeMatch Γ (`∀{A} B) R

-- @[aesop safe [constructors, cases]]
inductive PrefixHsTypeMatch : HsCtx HsTerm -> HsTerm -> HsTerm -> HsTerm -> Prop where
| refl :
  HsValidHeadVariable B Γ.is_stable ->
  PrefixHsTypeMatch Γ B T T
| arrow :
  PrefixHsTypeMatch (.empty::Γ) B V ([S]T) ->
  PrefixHsTypeMatch Γ (A → B) (A → V) T
| all :
  PrefixHsTypeMatch (.kind A::Γ) B V ([S]T) ->
  PrefixHsTypeMatch Γ (`∀{A} B) (`∀{A} V) T


-- @[aesop safe [constructors, cases]]
inductive HsVariant where -- what i am checking
| kind | type | term | ctx

-- @[simp]
abbrev HsJudgmentArgs : HsVariant -> Type
| .ctx => Unit
| .kind => HsTerm × HsTerm
| .type => HsTerm × HsTerm
| .term => HsTerm × HsTerm


-- @[aesop safe [constructors, cases]]
inductive HsJudgment : (v : HsVariant) -> HsCtx HsTerm -> HsJudgmentArgs v -> Prop where
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
  HsJudgment .ctx (.datatypeDecl A::Γ) ()
| wfclass :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .ctx Γ () ->
  HsJudgment .ctx (.classDecl A::Γ) ()

-- -----------------------------------
-- -- Implicits
-- -----------------------------------
-- | implicitArrI :
--   HsJudgment .type Γ (π, `★) ->
--   HsJudgment .type (.empty::Γ) (τ, `★) ->
--   HsValidHeadVariable π Γ.is_opent ->
--   HsJudgment .term (.type π :: Γ) ([S]t, τ) ->
--   HsJudgment .term Γ (t, π ⇒ τ) -- F a => τ

-- | implicitArrE :
--   HsJudgment .term Γ (t, π ⇒ τ) -> -- F a => τ
--   HsJudgment .term Γ (e, π) ->
--   τ' = τ β[e] ->
--   HsJudgment .type Γ (τ', `★) ->
--   HsJudgment .term Γ (t, τ')

/-
      A, Γ ⊢ [S]t : τ       Γ ⊢ A : □
 --------------------------------------------
             Γ ⊢ t : ∀ A. τ

Alternative : --- BOO!!
      A, Δ; [S]Γ ⊢ [S]t : τ       Δ ⊢ A : □
 --------------------------------------------
             Δ, Γ ⊢ t : ∀ A. τ

-/

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
  HsValidHeadVariable A Γ.is_classDecl -> -- is ClassCtor
  HsJudgment .type (.empty::Γ) (B, `★) ->
  HsJudgment .type Γ (A ⇒ B, `★)
| appk :
  HsJudgment .type Γ (f, A `-k> B) ->
  HsJudgment .type Γ (a, A) ->
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .kind Γ (B, `□) ->
  HsJudgment .type Γ (f `•k a, B)
| varTy :
  HsJudgment .ctx Γ () ->
  (Γ d@̈ x).is_datatypeDecl || (Γ d@̈ x).is_kind || (Γ d@̈ x).is_classDecl ->
  .some T = (Γ d@̈ x).get_type ->
  HsJudgment .kind Γ (T, `□) -> -- should be derivable?
  HsJudgment .type Γ (`#x, T)

------------------------------------
--- Terms
------------------------------------
| var :
  HsJudgment .ctx Γ () ->
  (Γ d@̈ x).is_term || (Γ d@̈ x).is_type -> -- (Γ d@̈ x).is_ctor
  .some T = (Γ d@̈ x).get_type ->
  HsJudgment .term Γ (`#x, T)
| lam :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .term (.type A :: Γ) (t, B) ->
  HsJudgment .type (.empty :: Γ) (B, `★) ->
  HsJudgment .term Γ (λ̈[ A ] t, A → B)
| lamt :
  HsJudgment .term (.kind A :: Γ) (t, τ) ->
  HsJudgment .kind Γ (A, `□) ->
  HsJudgment .term Γ (Λ̈[ A ]t, `∀{A} τ)
| app :
  HsJudgment .term Γ (t1, A → B) ->
  HsJudgment .term Γ (t2, A) ->
  B' = B β[t2] ->
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .type Γ (B', `★) ->
  HsJudgment .term Γ (t1 `• t2,  B')
| appt :
  HsJudgment .term Γ (t, `∀{A} τ) ->
  HsJudgment .type Γ (e, A) ->
  τ' = τ β[e] ->
  HsJudgment .term Γ (t `• e , τ')
| hslet :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .term Γ (t1,  A) ->
  B' = [S]B ->
  HsJudgment .term (.term A t1 :: Γ) (t2, B') ->
  HsJudgment .type Γ (B, `★) ->
  HsJudgment .term Γ (.HsLet A t1 t2, B)
| hsIte :
  HsJudgment .type Γ (A, `★) ->
  HsJudgment .type Γ (R, `★) ->
  HsJudgment .type Γ (B, `★) ->
  HsJudgment .type Γ (T, `★) ->
  HsJudgment .term Γ (p, A) ->
  HsJudgment .term Γ (s, R) ->
  HsJudgment .term Γ (i, B) ->
  HsJudgment .term Γ (t, T) ->
  StableHsTypeMatch Γ A R ->
  PrefixHsTypeMatch Γ A B T ->
  HsValidHeadVariable R Γ.is_datatypeDecl ->
  (p = `#n) ->
  -- HsValidHeadVariable p Γ.is_ctor ->
  HsJudgment .term Γ (.HsIte p s i t,  T)

notation:170 Γ:170 " ⊢κ " t:170 " : " A:170 => HsJudgment HsVariant.kind Γ (t, A)
notation:170 Γ:170 " ⊢τ " t:170 " : " A:170 => HsJudgment HsVariant.type Γ (t, A)
notation:170 Γ:170 " ⊢t " t:170 " : " A:170 => HsJudgment HsVariant.term Γ (t, A)
notation:170 "⊢s " Γ:170 => HsJudgment HsVariant.ctx Γ ()


-- def hs_judgment_ctx_wf : (v : HsVariant) -> {idx : HsJudgmentArgs v} -> HsJudgment v Γ idx -> ⊢s Γ
-- | .ctx , _ , x => x
-- | .kind, _ , x => match x with
--   | .ax h => h
--   | .arrowk h _ => hs_judgment_ctx_wf .kind h
-- | .type , _ , x => match x with
--   | .varTy h _ _ _ => hs_judgment_ctx_wf .ctx h
--   | .appk _ _ h _ => hs_judgment_ctx_wf .kind h
--   | .allt h _ =>  hs_judgment_ctx_wf .kind h
--   | .arrow h _ => hs_judgment_ctx_wf .type h
--   | .farrow h _ _ => hs_judgment_ctx_wf .type h
-- | .term , _ , x => match x with
--   | .lamt _ h2 => hs_judgment_ctx_wf .kind h2
--   | .appt _ h1 _ => hs_judgment_ctx_wf .type h1
--   | .implicitArrI h1 _ _ _ => hs_judgment_ctx_wf .type h1
--   | .implicitArrE h1 _ _ _ => hs_judgment_ctx_wf .term h1
--   | .var h _ _ => h
--   | .lam h _ _ => hs_judgment_ctx_wf .type h
--   | .app h _ _ _ _ => hs_judgment_ctx_wf .term h
--   | .hslet h _ _ _ _ => hs_judgment_ctx_wf .type h
--   | .hsIte h _ _ _ _ _ _ _ _ _ _ _ _ => hs_judgment_ctx_wf .type h

theorem hs_judgment_ctx_wf : (v : HsVariant) -> {idx : HsJudgmentArgs v} -> HsJudgment v Γ idx -> ⊢s Γ := by
intro v idx j;
induction j
all_goals try (constructor)
all_goals try (assumption)


def extract_kinding :
  Γ ⊢τ τ : k ->
  Γ ⊢κ k : `□
| .arrow h1 h2 => HsJudgment.ax (hs_judgment_ctx_wf .type h1)
| .farrow h1 h2 _ => HsJudgment.ax (hs_judgment_ctx_wf .type h1)
| .allt h1 h2 => HsJudgment.ax (hs_judgment_ctx_wf .kind h1)
| .appk _ _ _ h => h
| .varTy _ _ _ h => h


-- @[aesop safe [constructors, cases]]
inductive HsFrameWf : HsCtx HsTerm -> Frame HsTerm -> Prop where
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

notation:170 Γ:170 " ⊢s " f:170 => HsFrameWf Γ f
