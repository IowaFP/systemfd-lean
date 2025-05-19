import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.Uniqueness

@[simp]
def hs_kind_inversion : Γ ⊢κ k : w -> w = `□
| .ax _ => rfl
| .arrowk _ _ => rfl

@[simp]
def hs_extract_kinding : Γ ⊢τ t : k -> Γ ⊢κ k : `□
| .appk _ _ _ h => h
| .arrow h _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)
| .varTy _ _ _ h => h
| .farrow h _ _ => HsJudgment.ax (hs_judgment_ctx_wf .type h)
| .allt h _ => HsJudgment.ax (hs_judgment_ctx_wf .kind h)

@[simp]
def is_hs_kind : HsTerm -> Bool
| `★ => True
| a `-k> b => is_hs_kind a && is_hs_kind b
| _ => False

theorem kinding_classification_kind : (k : HsTerm) ->
  Γ ⊢κ k : w ->
  is_hs_kind k := by
intro k j
cases j <;> simp
case _ A B h1 h2 =>
  have lem1 := kinding_classification_kind A h1
  have lem2 := kinding_classification_kind B h2
  constructor; assumption; assumption
termination_by h => h.size

@[simp]
def is_hs_type : Ctx HsTerm -> HsTerm -> Bool
| Γ, .HsVar n =>
     (Γ d@ n).is_datatype || (Γ d@ n).is_kind
  -- && Option.map is_kind ((Γ d@ n).get_type) /= .none
| Γ, .HsBind2 .all A τ =>
  is_hs_kind A &&
  is_hs_type (.kind A :: Γ) τ
| Γ, .HsBind2 .arrow A B =>
  is_hs_type Γ A &&
  is_hs_type (.empty :: Γ) B
| Γ, .HsBind2 .farrow A B =>
  is_hs_type Γ A &&
  is_hs_type (.empty :: Γ) B
| Γ, .HsCtor2 .appk A B =>
  is_hs_type Γ A &&
  is_hs_type Γ B
| _, _ => False


theorem typing_classification_type : (t k : HsTerm) ->
  Γ ⊢τ t : k ->
  is_hs_type Γ t := by
intro t k j; cases j <;> simp
case _ A B h1 h2 =>
  constructor
  apply kinding_classification_kind A h1
  apply typing_classification_type B `★ h2
case _ A B h1 h2 =>
  constructor
  apply typing_classification_type A `★ h1
  apply typing_classification_type B `★ h2
case _ A B h1 _ h2 =>
  constructor
  apply typing_classification_type A `★ h1
  apply typing_classification_type B `★ h2
case _ f A a h1 _ h2 _ =>
  constructor
  apply typing_classification_type f _ h2
  apply typing_classification_type a A h1
case _ h _ _ => simp at h; assumption
termination_by h => h.size

theorem typing_classification_kind : (t k : HsTerm) ->
  Γ ⊢τ t : k ->
  is_hs_kind k := by
intro t k j
cases j <;> try simp
all_goals (case _ h => apply kinding_classification_kind k h)
