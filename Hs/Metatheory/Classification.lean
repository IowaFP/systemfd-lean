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
