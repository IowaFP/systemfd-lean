import Core.Term
import Core.Reduction
import Core.Typing

theorem Kinding.invert_eq_kind : (G&Δ ⊢ (A ~[K]~ B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Kinding.invert_arr_kind : (G&Δ ⊢ (A -:> B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Kinding.inver_all_kind : (G&Δ ⊢ (∀[A] B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Typing.lamt_unique : (G&Δ, Γ ⊢ (Λ[A] b) : t) -> (∃ B', t = ∀[A] B') := by
intros j; cases j; simp

theorem Typing.lam_unique : (G&Δ, Γ ⊢ λ[A]b : t) -> (∃ B', (t = (A -:> B'))) := by
intros j; cases j; simp

theorem Typing.lam_unique2 : (G&Δ, Γ ⊢ λ[A]b : (A' -:> B)) -> A = A' := by
intros j; cases j; simp

theorem Typing.refl_unique : (G&Δ, Γ ⊢ refl! A : T) -> ∃ K, (T = (A ~[K]~ A)) := by
intros j; cases j; simp
