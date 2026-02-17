import Translation.Ty
import Core.Typing
import Surface.Typing
-- Translation preservies kinding relation

def trans_global : List Surface.Global -> Option (List Global) := sorry
def trans_kis : List Surface.Kind -> List Kind := sorry

theorem Translation.Ty.Sound :
  G&Δ ⊢s T : K ->
  trans_ki K = K' ->
  trans_global G = some G' ->
  trans_kis Δ = Δ' ->
  trans_ty G' Δ' T = some T' ->
  G'&Δ' ⊢ T' : K' := by sorry
