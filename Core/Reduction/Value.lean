import LeanSubst
import Core.Term
import Core.Reduction.Definition

open LeanSubst

namespace Core

theorem Value.sound : Value G t -> ∀ t', ¬ (G ⊢ t ~> t')
| .refl, _, r => nomatch r

end Core
