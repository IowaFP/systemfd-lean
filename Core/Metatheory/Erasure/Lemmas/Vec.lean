import Core.Metatheory.Erasure.Definition

open LeanSubst
open Lilac

namespace Core

theorem erasure_match_cong {ss ss' : Lilac.Fun.Vec Term m}:
  (∀ (j : Fin m), j ≠ i → ss j = ss' j) →
  ∀ (j : Fin m), j ≠ i → ⟦ss j⟧ = ⟦ss' j⟧ := by sorry
