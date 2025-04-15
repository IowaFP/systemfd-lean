import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Algorithm

theorem compile_beta_kind_type :
  (j1 : (.kind A::Γ) ⊢τ b : B) ->
  compile_type (.kind A::Γ) b B j1 = .some b' ->
  (j2 : Γ ⊢τ t : A) ->
  compile_type Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by sorry


theorem compile_beta_empty_type :
  (j1 : (.empty::Γ) ⊢τ b : B) ->
  compile_type (.empty::Γ) b B j1 = .some b' ->
  (j2 : Γ ⊢τ t : A) ->
  compile_type Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by sorry

theorem compile_beta_empty_term :
  (j1 : (.empty::Γ) ⊢τ b : B) ->
  compile_type (.empty::Γ) b B j1 = .some b' ->
  (j2 : Γ ⊢t t : A) ->
  compile_term Γ t A j2 = .some t' ->
  (j3 : Γ ⊢τ (b β[t]) : (B β[t])) ->
  compile_type Γ (b β[t]) (B β[t]) j3 = .some (b' β[t']) := by sorry
