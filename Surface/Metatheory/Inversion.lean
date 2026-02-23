import Surface.Typing
import Surface.Metatheory.Substitution

namespace Surface



theorem GlobalWf.extract_kinding :
  ⊢s G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢s T : .base b := by
intro wf h
induction G generalizing x T Δ
case _ => simp [lookup_type, lookup] at *
case _ hd tl ih =>
    sorry


theorem Typing.well_typed_terms_have_base_kinds :
  ⊢s G ->
  G&Δ, Γ ⊢s t : A -> ∃ b, G&Δ ⊢s A : .base b := by
intro wf j; induction j
case var => constructor; assumption
case global h => apply GlobalWf.extract_kinding wf; assumption
case lam h =>
  rcases h with ⟨_, h⟩
  exists b`★; constructor; assumption; assumption
case lamt h => exists b`★

case app h _ =>
  rcases h with ⟨_, h⟩
  cases h; case _ b _ _  =>
  exists b
case appt h =>
  rcases h with ⟨b, h⟩
  cases h; case _ h1 e h2 =>
  exists b`★;
  subst e;
  apply Kinding.beta h2 h1

case mtch => assumption


end Surface
