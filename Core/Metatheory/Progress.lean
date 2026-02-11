import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.ValueSoundness

theorem progress_lemma :
  ⊢ G ->
  Γ = [] ->
  G&Δ,Γ ⊢ t : T ->
  Value G t ∨ t = `0 ∨ ∃ t', G ⊢ t ~> t' := by
intro wf e j
induction j
case var => subst e; simp at *
case global =>
  subst e

  sorry
case mtch =>
  subst e
  sorry
case guard =>
  subst e
  sorry
case lam => apply Or.inl; apply Value.lam
case lamt => apply Or.inl; apply Value.lamt
case zero => apply Or.inr; apply Or.inl; rfl
case refl => apply Or.inl; apply Value.refl
case app b _ _ _ _ _ _ _ ih1 ih2 =>
  cases b
  case _ =>
    cases ih2 e
    case _ => sorry
    case _ => sorry
  case _ =>
    sorry

case appt => sorry
case cast t A _ _ _ _ j _ ih =>
  cases ih e
  case _ h =>
    have lem := refl_is_val j h
    cases lem;
    case _ lem =>
      rcases lem with ⟨e1, e2⟩; subst e1; subst e2
      apply Or.inr; apply Or.inr; exists t; apply Red.cast
    case _ lem =>
      rcases lem with ⟨c1, c2, e⟩; subst e
      apply Or.inr; apply Or.inr
      exists (t ▹ c1) `+  (t ▹ c2)
      apply Red.ctor2_map2; simp; simp
  case _ lem =>
     cases lem
     case _ h => subst h; apply Or.inr; apply Or.inr; exists `0; apply Red.ctor2_absorb2 (v := .cast); simp
     case _ h =>
       rcases h with ⟨c', h⟩
       apply Or.inr; apply Or.inr; exists (t ▹ c')
       apply Red.ctor2_congr2 (by simp) h

case sym ih =>
  cases ih e
  case _ ih => sorry
  case _ ih =>
    cases ih
    case _ ih => sorry
    case _ ih => sorry

case seq ih1 ih2 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry


case appc ih1 ih2 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case arrowc ih1 ih2 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case fst ih1 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case snd ih1 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case allc Γ _ ih1 =>
  have e' : List.map (λ x => x[+1]) Γ = [] := by rw[e]; simp
  cases ih1 e'
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case apptc ih1 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry

case choice ih1 ih2 =>
  cases ih1 e
  case _ ih1 => sorry
  case _ ih1 =>
    cases ih1
    case _ ih1 => sorry
    case _ ih1 => sorry
