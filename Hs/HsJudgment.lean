import Hs.HsTerm
import Hs.HsCtx

def pad_empty_ctx : Nat -> HsCtx HsTerm
| 0 => [.empty]
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
  HsJudgment .TermJ Γ (k, `□) ->
  HsJudgment .CtxJ (.kind k ::  Γ) ()
| wftype :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TermJ Γ (A, `★) ->
  HsJudgment .CtxJ (.type A :: Γ) ()
| wfdatatypeDecl :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TermJ Γ (k, `□) ->
  ∀ p: i < ctors.length, HsJudgment .TermJ (pad_empty_ctx i ++ Γ) (ctors[i]'(by assumption), `★) ->
  HsJudgment .CtxJ (.datatypeDecl k ctors :: Γ) ()
| wfterm :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TermJ Γ (A, `★) ->
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
  FrameMetadata.get_type (Γ s@ x) = .some T ->
  HsJudgment .TypeJ Γ (`#x, T)

| arrowt :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (A, `★) ->
  HsJudgment .TypeJ (.empty :: Γ) (B, `★) ->
  HsJudgment .TypeJ Γ (A → B, `★)
| allt :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (A, `★) ->
  HsJudgment .TypeJ (.type A :: Γ) (B, `★) ->
  HsJudgment .TypeJ Γ (`∀{A} B, `★)
| appt :
  HsJudgment .CtxJ Γ () ->
  HsJudgment .TypeJ Γ (T, k `-k> k') ->
  HsJudgment .TypeJ Γ (A, k) ->
  HsJudgment .TypeJ Γ (T `•k A, `★)
