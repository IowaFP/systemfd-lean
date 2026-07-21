import Core.Ty
import Core.Term
import Core.Typing

import Core.Ppcc.Basic

namespace Core.Ppcc

theorem EqGraph.ask_type_sound {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv} {eG : EqGraph G Δ Γ} {c : Term} {j : G&Δ, Γ ⊢ c : (T1 ~[K]~ T2)}:
  eG.ask G wf Δ Γ K T1 T2 = some ⟨c, j⟩ ->
  G&Δ, Γ ⊢ c : (T1 ~[K]~ T2) :=
  by intro h; apply j


theorem env_consistency {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv} :
  TyEnv.is_consistent G wf Δ Γ = some () ->
  ∀ T1 T2 K, T1 ≠ T2 -> ¬ (G&Δ, Γ ⊢ c : (gt#T1 ~[K]~ gt#T2))
:= by
 intro h T1 T2 K ne j
 unfold TyEnv.is_consistent at h; simp at h

 sorry

end Core.Ppcc
