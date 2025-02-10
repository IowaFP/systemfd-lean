import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Judgment
import SystemFD.Ctx

@[simp]
abbrev class_idx (t A : Term) : JudgmentArgs v :=
  match v with
  | .prf => (t, A)
  | .wf => ()

@[simp]
abbrev ClassType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (_, A) => A = .kind ∨ (Γ ⊢ A : .kind) ∨ (∃ K, Γ ⊢ A : .const K)
| .wf => λ () => ∀ x T, Frame.get_type (Γ d@ x) = .some T -> Γ ⊢ T : .kind ∨ (∃ K, Γ ⊢ T : .const K)

theorem classification_lemma : Judgment v Γ ix -> ClassType Γ v ix := by
intro j; induction j <;> simp at *
all_goals (try simp [*])
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ j1 j2 ih1 ih2 =>
  cases ih2
  case _ ih2 =>
    cases ih2; case _ ih2 =>
      apply Or.inr; apply Or.inl; apply ih2
  case _ ih2 =>
  cases ih2; case _ K ih2 =>
    cases ih2
case _ j _ _ => apply Or.inl; constructor; apply judgment_ctx_wf j
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
