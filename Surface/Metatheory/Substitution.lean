
import Surface.Typing

open LeanSubst
namespace Surface

theorem Kinding.subst Δσ (σ : Subst Ty) :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢s σ i : K) ->
  G&Δ ⊢s A : K ->
  G&Δσ ⊢s A[σ] : K
:= by
  intro h j
  induction j generalizing Δσ σ <;> simp
  case var Δ x K j => apply h x K j
  case global j => apply global j
  case arrow j1 j2 ih1 ih2 =>
    apply arrow
    apply ih1 _ _ h
    apply ih2 _ _ h
  case all K Δ P j ih =>
    sorry -- replace ih := ih (K :: Δσ) σ.lift (subst_lift K h)
    -- simp at ih
    -- apply all ih
  case app j1 j2 ih1 ih2 =>
    apply app
    apply ih1 _ _ h
    apply ih2 _ _ h


theorem Kinding.beta :
  G&(T::Δ) ⊢s A : K ->
  G&Δ ⊢s t : T ->
  G&Δ ⊢s A[su t::+0] : K
:= by
  intro j1 j2
  apply Kinding.subst Δ (su t::+0) _ j1
  intro i K h; cases i <;> simp [Surface.inst_getElem?_KindEnv] at *
  case _ => subst h; exact j2
  case _ i => apply var h

end Surface
