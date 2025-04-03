import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Metatheory.Classification

set_option maxHeartbeats 500000

@[simp]
abbrev WfKindCompleteType : (v : JudgmentVariant) -> Ctx Term -> JudgmentArgs v -> Prop
| .prf => λ Γ => λ (t, τ) => τ = .kind -> Γ = [] -> Γ ⊢ t : τ -> wf_kind t = .some ()
| .wf  => λ _ => λ () => true


theorem wf_kind_complete :
  ⊢ Γ ->
  Judgment v Γ idx ->
  WfKindCompleteType v Γ idx
:= by
intros wf j; induction j <;> simp at *;
case _ =>
  intro e1 e2 h; subst e1; subst e2
  cases h; case _ h _ => cases h
case _ gt _ =>
  intro e1 e2 h; subst e1; subst e2;
  case _ =>
  cases gt;
case _ h1 h2 ih1 ih2 =>
  intro e2 h; subst e2;
  rw[Option.bind_eq_some]; exists ();
  replace ih1 := ih1 wf rfl h1
  replace ih2 := ih2 wf rfl h2
  apply And.intro;
  assumption
  rw[Option.bind_eq_some]; exists ();
case _ =>
  intro e; subst e;
  case _ j =>
  have lem := classification_lemma j; simp at lem;
  cases lem;
  case _ h => cases h; case _ h => cases h
  case _ h =>
    cases h; case _ w h =>
    cases h; case _ w1 h =>
    cases h; cases w1
case _ =>
  intro e1 e2; subst e1; subst e2
  intro h;
  cases h; case _ h _ => cases h;
case _ =>
  intro e h; subst e;
  cases h; case _ h => cases h;
all_goals (
  intro e1 e2 h; subst e1; subst e2;
  cases h;
)
case _ h =>
  sorry
case _ h =>
  sorry
case _ h =>
  sorry
