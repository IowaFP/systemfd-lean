import Surface.Term
import Core.Term

import Translation.Term

theorem Translation.Ty.Weaken {T : Surface.Ty} {T' : Core.Ty} :
  T.translate G' Δ' = some T' ->
  (T[+1]).translate G' (K' :: Δ') = some (T'[+1]) := by sorry
