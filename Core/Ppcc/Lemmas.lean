import Core.Ty
import Core.Term
import Core.Typing

import Core.Ppcc.Basic

namespace Core.Ppcc

-- maybe need some predicate to say what makes G well formed?
theorem EqGraph.find_preserves_type (eqG : EqGraph) :
  eqG.find T1 T2 = some t ->
  G&Δ, Γ ⊢ t : (T1 ~[K]~ T2) := sorry


end Core.Ppcc
