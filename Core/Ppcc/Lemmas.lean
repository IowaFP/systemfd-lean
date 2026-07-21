import Core.Ty
import Core.Term
import Core.Typing

import Core.Ppcc.Basic

namespace Core.Ppcc

theorem EqGraph.ask_type_sound {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv} {eG : EqGraph G Δ Γ} {c : Term} {j : G&Δ, Γ ⊢ c : (T1 ~[K]~ T2)}:
  eG.ask G wf Δ Γ K T1 T2 = some ⟨c, j⟩ ->
  G&Δ, Γ ⊢ c : (T1 ~[K]~ T2) :=
  by intro h; apply j

end Core.Ppcc
