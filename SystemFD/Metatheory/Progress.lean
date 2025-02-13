
import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Reduction
import SystemFD.Metatheory.Weaken

-- Neutral terms are values with variables
inductive νT : Term -> Prop where
| lam : νT (`λ[a] b)
| lamt : νT (Λ[A] b)
| refl : νT (refl! _)
| var :  νT #n
| appNe : νT t
        -> νT (t `@ t')
| apptNe : νT t
         -> νT (t `@t t')

theorem progress_νT : ⊢ Γ -> (Γ ⊢ A : ★) -> (Γ ⊢ t : A) -> νT t ∨ ∃ t', Red Γ t t' := by
intros wf Astar typingJ;
cases typingJ;
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => sorry
case _ => cases Astar
case _ => sorry
case _ => cases Astar
case _ => sorry
case _ => cases Astar
case _ => sorry
case _ => sorry
case _ => apply Or.inl .lam
case _ =>
  sorry
case _ => apply Or.inl .lamt
case _ => sorry
case _ => sorry
case _ => apply Or.inl .refl
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
case _ => cases Astar
