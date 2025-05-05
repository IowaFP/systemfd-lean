import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Algorithm


def subst_compile_kind : {Γ Δ : Ctx HsTerm} -> {σ : Subst HsTerm} -> {σ' : Subst Term} ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢κ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->

  (j : Γ ⊢κ t : k) ->
  compile_kind Γ t k j = .some t' ->
  ⊢s Δ ->

  (sj : Δ ⊢κ ([σ]t) : ([σ]k)) ->
  compile_kind Δ ([σ]t) ([σ]k) sj = .some ([σ']t') := by

sorry





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

def compile_replace_empty :
  (j1 : (.empty :: Γ) ⊢τ τ : k) ->
  (j2 : (f :: Γ) ⊢τ τ : k) ->
  compile_type (.empty :: Γ) τ k j1 = .some τ' ->
  compile_type (f :: Γ) τ k j2 = .some τ' := by sorry
