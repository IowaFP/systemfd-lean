import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import Hs.Metatheory.Preservation1
import SystemFD.Algorithm.Soundness2


theorem compile_preserves_ctor_frame :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (∀ v, CompileCtxPred v) ->
  ⊢ Γ' ->
  HsFrameWf Γ (.ctor T) ->
  (j : Γ ⊢τ T : `★) ->
  compile_type Γ T `★ j = .some T' ->
  FrameWf Γ' (.ctor T') := by
intro h cc wf j1 j cj;
constructor;
-- apply compile_preserves_types (cc .kind) wf h
sorry
case _ => cases j1; sorry
