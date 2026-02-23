import Surface.Typing
import Surface.Metatheory.Substitution

namespace Surface


theorem PrefixTypeMatch.base_kinding :
  G&Δ ⊢s A : .base b1 ->
  G&Δ ⊢s B : .base b2 ->
  PrefixTypeMatch Δ A B T ->
  ∃ b, G&Δ ⊢s T : .base b := by
intro j1 j2 j3
induction j3 generalizing b1 b2
case refl => exists b2
case arrow ih =>
  cases j1; cases j2
  case _ h1 _ _ _ h2 =>
  apply ih h1 h2
case all ih =>
  cases j1; cases j2
  case _ h1 h2 =>
  replace ih := ih h1 h2
  cases ih; case _ b h =>
  exists b; sorry -- apply Kinding.strengthening h



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
