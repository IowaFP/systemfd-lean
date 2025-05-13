import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.Weaken
import Hs.Metatheory.Substitution
import Hs.Metatheory.Uniqueness


def hs_kind_inversion : Γ ⊢κ k : w -> w = `□
| .ax _ => rfl
| .arrowk _ _ => rfl

def hs_extract_kinding : Γ ⊢τ t : k -> Γ ⊢κ k : `□
| .appk _ _ _ h => h
| .arrow h _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)
| .varTy _ _ _ h => h
| .farrow h _ _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)
| .allt h _ => HsJudgment.ax (hs_judgment_ctx_wf .kind h)


def is_hs_kind : HsTerm -> Option Unit
| `★ => .some ()
| a `-k> b => do
  let _ <- is_hs_kind a
  let _ <- is_hs_kind b
  .some ()
| _ => .none

def is_hs_type : Ctx HsTerm -> HsTerm -> Option Unit
| Γ, .HsVar n =>
  if (Γ d@ n).is_datatype || (Γ d@ n).is_kind
  then .some () else .none
  -- && Option.map is_kind ((Γ d@ n).get_type) /= .none
| Γ, .HsBind2 .all A τ => do
  let _ <- is_hs_kind A
  let _ <- is_hs_type (.kind A :: Γ) τ
  .some ()
| Γ, .HsBind2 .arrow A B => do
  let _ <- is_hs_type Γ A
  let _ <- is_hs_type (.empty :: Γ) B
  .some ()
| Γ, .HsBind2 .farrow A B => do
  let _ <- is_hs_type Γ A
  let _ <- is_hs_type (.empty :: Γ) B
  .some ()
| Γ, .HsCtor2 .appk A B => do
  let _ <- is_hs_type Γ A
  let _ <- is_hs_type Γ B
  .some ()
| _, _ => .none
