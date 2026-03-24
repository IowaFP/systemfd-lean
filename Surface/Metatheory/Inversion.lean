import Surface.Typing
import Surface.Metatheory.Substitution

namespace Surface


theorem EntryWf.kinding :
  ⊢s G ->
  EntryWf G e ->
  e.type = some T ->
  ∃ b, G&Δ ⊢s T : .base b := by sorry
-- intro wf h1 h2
-- induction e  <;> simp [Entry.type] at *
-- case _ a =>
--   subst a; cases h1
--   case _ h _ _ =>
--   -- arbitrary weakening
--   sorry
-- case _ a =>
--   subst a; cases h1
-- case defn =>  sorry
-- case instty => sorry

theorem GlobalWf.extract_kinding :
  ⊢s G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢s T : .base b := by
intro wf h
simp [lookup_type] at h
generalize zdef : lookup x G = z at *
cases z <;> simp [Option.map] at *
apply EntryWf.kinding wf sorry h
-- induction G generalizing x T Δ <;> simp [lookup] at *
-- case _ => subst zdef; simp at h
-- case _ hd tl ih =>
--     cases hd
--     cases wf; case _ wftl wfg =>
--     cases wfg
--     split at zdef <;> simp at *
--     case _ e => subst e; subst z; simp [Entry.type] at h

--     sorry



theorem Typing.well_typed_terms_have_base_kinds :
  ⊢s G ->
  G&Δ, Γ ⊢s t : A -> ∃ b, G&Δ ⊢s A : .base b := by
intro wf j; induction j
case var => constructor; assumption
case global h => apply GlobalWf.extract_kinding wf; assumption
case lam h =>
  rcases h with ⟨_, h⟩
  exists b`★; constructor; assumption; assumption
case lamP h =>
  rcases h with ⟨_, h⟩
  exists b`★; constructor; assumption; assumption
case lamt h => exists b`★
case app h _ =>
  rcases h with ⟨_, h⟩
  cases h; case _ b _ _  =>
  exists b
-- case appP h _ =>
--   rcases h with ⟨_, h⟩
--   cases h; case _ b _ _  =>
--   exists b
case appt h =>
  rcases h with ⟨b, h⟩
  cases h; case _ h1 e h2 =>
  exists b`★;
  subst e;
  apply Kinding.beta h2 h1

case mtch => assumption
case annot => assumption


end Surface
