import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import Hs.Metatheory.Preservation1
import SystemFD.Algorithm.Soundness2


theorem compile_type_match :
 -- (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jA : Γ ⊢τ A : `★) ->
 compile_type Γ A `★ jA = .some A' ->
 (jA : Γ ⊢τ R : `★) ->
 compile_type Γ R `★ jR = .some R' ->
 StableHsTypeMatch Γ A R -> StableTypeMatch Γ' A' R' := by sorry


theorem compile_stable_match :
 -- (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jA : Γ ⊢τ A : `★) ->
 compile_type Γ A `★ jA = .some A' ->
 (jR : Γ ⊢τ R : `★) ->
 compile_type Γ R `★ jR = .some R' ->
 StableHsTypeMatch Γ A R -> StableTypeMatch Γ' A' R' := by sorry


theorem compile_prefix_match :
 -- (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jA : Γ ⊢τ A : `★) ->
 compile_type Γ A `★ jA = .some A' ->
 (jR : Γ ⊢τ R : `★) ->
 compile_type Γ R `★ jR = .some R' ->
 (jT : Γ ⊢τ T : `★) ->
 compile_type Γ T `★ jT = .some T' ->
 PrefixHsTypeMatch Γ A R T -> PrefixTypeMatch Γ' A' R' T' := by sorry

theorem compile_preserves_vhv_types test σtest :
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jT : Γ ⊢τ T : `★) ->
 compile_type Γ T `★ jT = .some T' ->
 HsValidHeadVariable T test ->
 ValidHeadVariable T' σtest := by sorry


theorem compile_preserves_vhv_terms test σtest :
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jT : Γ ⊢t T : τ) ->
 compile_term Γ T τ jT = .some T' ->
 HsValidHeadVariable T test ->
 ValidHeadVariable T' σtest := by sorry
