import Hs.HsTerm
import Hs.HsCtx

def pad_empty_ctx : Nat -> HsCtx HsTerm
| 0 => []
| n + 1 => .empty :: pad_empty_ctx n


inductive JIdx where
| CtxJ | TermJ | TypeJ | KindJ

@[simp]
abbrev JudgmentType : JIdx -> Type
| .CtxJ => Unit
| .TermJ => HsTerm × HsTerm
| .KindJ => HsTerm × HsTerm
| .TypeJ => HsTerm × HsTerm

inductive HsJudgment : (i : JIdx) -> HsCtx HsTerm -> JudgmentType i -> Prop where
| wfnil : HsJudgment .CtxJ [] ()
| wfempty :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .CtxJ (.empty :: Γ) ()
| wfkind :
  HsJudgment .CtxJ Γ  () ->
  HsJudgment .KindJ Γ (k, `□) ->
  HsJudgment .CtxJ (.kind k ::  Γ) ()
| wftype :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (A, `★) ->
  HsJudgment .CtxJ (.type A :: Γ) ()
| wfdatatypeDecl :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .KindJ Γ (T, `□) ->
  ∀ p: i < ctors.length, HsJudgment .TypeJ (pad_empty_ctx (i - 1) ++ .type T :: Γ) (ctors[i]'(by assumption), `★) ->
  HsJudgment .CtxJ (.datatypeDecl k ctors :: Γ) ()
| wfterm :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (A, `★) ->
  HsJudgment .TermJ Γ (t, A) ->
  HsJudgment .CtxJ (.term A t :: Γ) ()

| wfstar :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .KindJ Γ (`★, `□)
| wfkarrow :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .KindJ Γ (κ1, `□) ->
  HsJudgment .KindJ Γ (κ2, `□) ->
  HsJudgment .KindJ Γ (κ1 `-k> κ2, `□)

| varTy :
  HsJudgment .CtxJ Γ () ->
  (Γ s@ x) = .tycon T ∨ (Γ s@ x) = .kind T ->
  HsJudgment .TermJ Γ (`#x, T)

| arrow :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (A, `★) ->
  HsJudgment .TypeJ (.empty :: Γ) (B, `★) ->
  HsJudgment .TypeJ Γ (A → B, `★)
| all :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .KindJ Γ (A, `□) ->
  HsJudgment .TypeJ (.kind A :: Γ) (B, `★) ->
  HsJudgment .TypeJ Γ (`∀{A} B, `★)
| appk :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (T, k `-k> k') ->
  HsJudgment .TypeJ Γ (A, k) ->
  HsJudgment .TypeJ Γ (T `•k A, k')


notation:170 Γ:170 " ⊢s " t:170 " : " A:170 => HsJudgment JIdx.TermJ Γ (t, A)
notation:170 "⊢s " Γ:170 => HsJudgment JIdx.CtxJ Γ ()

theorem hs_judgment_ctx_wf : HsJudgment v Γ idx -> HsJudgment .CtxJ Γ () := by
intro j
induction j
all_goals try simp [*]
case _ => constructor
case _ ih => constructor; apply ih
case _ j _ _ ih => constructor; apply j; assumption
case _ j _ _ ih => constructor; apply j; assumption
case _ j _ _ ih => constructor; assumption; assumption; assumption
case _ j _ h _ ih => constructor; assumption; assumption; assumption

inductive HsFrameWf : HsCtx HsTerm -> HsFrame HsTerm -> Prop
| empty :
  ⊢s Γ ->
  HsFrameWf Γ .empty
| kind:
  Γ ⊢s K : `★ ->
  HsFrameWf Γ (.kind K)
| type:
  Γ ⊢s A : `★ ->
  HsFrameWf Γ (.type A)
| datatypeDecl:
  Γ ⊢s T : `★ ->
  ∀ p: i < ctors.length, HsJudgment .TermJ (pad_empty_ctx (i - 1) ++ Γ) (ctors[i]'(by assumption), `★) ->
  HsFrameWf Γ (.datatypeDecl T ctors)

notation:170 Γ:170 " ⊢s " f:170 => HsFrameWf Γ f
