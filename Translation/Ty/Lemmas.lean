import Translation.Ty
import Translation.Global

import Core.Typing
import Surface.Typing
-- Translation preservies kinding relation


theorem Translation.Ty.Sound :
  G&Δ ⊢s T : K ->
  trans_ki K = K' ->
  trans_global G = some G' ->
  trans_kis Δ = Δ' ->
  trans_ty G' Δ' T = some T' ->
  G'&Δ' ⊢ T' : K' := by sorry
