import LeanSubst
import Core.Typing

open LeanSubst

theorem subst_lift [RenMap T] (σ : Subst T) :
  x < n ->
  rep Subst.lift σ n x = re x
:= by
  intro h; induction n generalizing x σ <;> simp [rep]
  cases h
  case _ n ih =>
  cases x <;> simp [Subst.lift]
  case _ i =>
  have lem : i < n := by omega
  replace ih := @ih i σ lem
  rw [ih]

theorem Kinding.closed_rep :
  G;Δ ⊢ A : K ->
  ∀ (σ : Subst Ty), A[rep Subst.lift σ Δ.length:_] = A
:= by
  intro j; induction j <;> intro σ <;> simp
  case var Δ x K j =>
    have lem : x < Δ.length := by sorry
    rw [subst_lift σ lem]; simp
  case arrow ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp
  case all ih =>
    replace ih := ih σ
    simp at ih; exact ih
  case app ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp
  case eq ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp

theorem Kinding.closed : G;[] ⊢ A : K -> ∀ σ, A[σ] = A := by
  intro j; apply closed_rep j

-- theorem GlobalWf.closed {G : List Global} :
--   GlobalWf G g ->
--   some T = g.type ->
--   ∀ σ, T[σ] = T
-- := by
--   intro j h
--   induction G
--   sorry

theorem Kinding.rename Δr (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  G;Δ ⊢ A : K ->
  G;Δr ⊢ A[r] : K
:= by
  intro h j
  induction j generalizing Δr r <;> simp
  case var Δ x K j =>
    simp [Ren.to]; apply Kinding.var
    rw [h x] at j; exact j
  case global j => apply Kinding.global j
  case arrow ih1 ih2 => apply Kinding.arrow (ih1 _ _ h) (ih2 _ _ h)
  case all K Δ P j ih =>
    replace ih := ih (K::Δr) r.lift (by {
      intro i; cases i <;> simp [Ren.lift]
      case _ i => exact h i
    })
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    apply Kinding.all ih
  case app ih1 ih2 => apply Kinding.app (ih1 _ _ h) (ih2 _ _ h)
  case eq ih1 ih2 => apply Kinding.eq (ih1 _ _ h) (ih2 _ _ h)

theorem Kinding.weaken : G;Δ ⊢ A : K -> G;(T::Δ) ⊢ A[+1] : K := by
  intro j; apply rename (T::Δ) (· + 1) _ j
  intro i; cases i <;> simp

theorem Typing.rename_type Δr (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  G;Δ,Γ ⊢ t : A ->
  G;Δr,Γ.map (·[r]) ⊢ t[r:Ty] : A[r]
:= by
  intro h j; induction j generalizing Δr r <;> simp
  case var j1 j2 =>
    apply Typing.var
    simp; apply Exists.intro _
    apply And.intro j1 rfl
    apply Kinding.rename _ r h j2
  case global j1 j2 =>
    sorry
  case mtch => sorry
  case guard => sorry
  case lam => sorry
  case app => sorry
  case lamt => sorry
  case appt => sorry
  case cast => sorry
  case refl => sorry
  case sym => sorry
  case seq => sorry
  case appc => sorry
  case arrowc => sorry
  case fst => sorry
  case snd => sorry
  case allc => sorry
  case apptc => sorry
  case zero => sorry
  case choice => sorry
