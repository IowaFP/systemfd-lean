import LeanSubst
import Core.Term
import Core.Term.Spine
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Rename
import Core.Metatheory.Substitution
import Core.Metatheory.GlobalWf
import Core.Metatheory.Uniqueness
import Core.Metatheory.Inversion
import Core.Metatheory.SpineType

open LeanSubst

theorem instance_type_preservation :
  ⊢ G ->
  G&Δ, Γ ⊢ g#x : T ->
  is = instances x G ->
  ∀ t ∈ is, ∀ Δ Γ, G&Δ, Γ ⊢ t : T := by
intro wf j h t t_in_is
sorry

theorem lookup_defn_type_sound :
  ⊢ G ->
  lookup x G = .some (Entry.defn y T t) ->
  ∀ Δ Γ, G&Δ, Γ ⊢ t : T := by
intro wf h
induction G <;> simp [lookup] at *
case _ hd tl ih =>
  cases wf; case _ wfh wft =>
  cases hd <;> simp [lookup] at *
  case data =>
    sorry
  case opent => sorry
  case openm => sorry
  case defn => sorry
  case inst => sorry
  case instty =>
    split at h
    cases h
    replace ih := ih wfh h
    sorry -- need weakening on globals



theorem Typing.foldr_preservation_choiceₗ :
    G&Δ ⊢ B : .base b ->
    G&Δ, Γ ⊢ a : B ->
    (∀ t ∈ is,  G&Δ, Γ ⊢ t : B) ->
    G&Δ, Γ ⊢ List.foldr (λ t acc => t `+ acc) a is : B := by
intro h1 h2 h3 ; induction is using List.foldr.induct <;> simp at *
assumption
case _ ih =>
  apply Typing.choice
  apply h1;
  apply h3.1
  apply ih h3.2

theorem Typing.foldr_preservation :
  G&Δ ⊢ T : .base b ->
  (∀ t ∈ is, G&Δ, Γ ⊢ t : T) ->
  G&Δ, Γ ⊢ List.foldr (·`+·) `0 is : T := by
intro j h
induction is <;> simp at *
constructor; assumption
case _ hd tl ih =>
  apply Typing.choice
  apply j
  apply h.1
  apply ih h.2


theorem fix_quantifiers {is : List Term} {Δ : List Kind} {Γ : List Ty} :
  (∀ t ∈ is, ∀ Δ Γ, G&Δ, Γ ⊢ t : T) ->
  (∀ t ∈ is, G&Δ, Γ ⊢ t : T) := by
intro h
intro t h1
apply h t h1


theorem type_match_spine_type_lemma :
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  SpineType G Δ Γ sp A B := by
intro j
induction j
case refl t =>

  sorry
case arrow t => sorry
case all t => sorry

theorem preservation_prefix_match_lemma :
  ⊢ G ->
  a.spine = some (x, sp) ->
  G&Δ,Γ ⊢ a : A ->
  G&Δ,Γ ⊢ a.apply ξ : R ->
  G&Δ,Γ ⊢ t : B ->
  StableTypeMatch Δ A R -> -- R is the return type of A
  PrefixTypeMatch Δ A B T -> -- T is B's return type and A and B have same prefixes
  G&Δ,Γ ⊢ t.apply ξ : T := by
intro wf h1 h2 h3 h4 h5 h6
induction ξ generalizing G Δ Γ A R B T a t x sp
case _ =>
   simp [Term.apply] at *
   have e := Typing.spine_term_unique_typing h2 h3 h1; cases e
   -- have e := StableTypeMatch.prefix_type_match_forced_refl h5 h6; cases e
   sorry
   -- assumption
case _ hd tl ih =>
    have lem : (hd :: tl) = [hd] ++ tl := by simp
    rw[lem, Spine.apply_spine_compose] at h3; rw[lem, Spine.apply_spine_compose]; clear lem
    have lem := Typing.inversion_apply_spine wf h3
    rcases lem with ⟨B', h1, h2, _, h3⟩
    cases hd <;> simp [Term.apply] at *
    case type hd =>
      cases h5
      case refl =>
        cases h2; case _ e =>
        -- subst e
        replace ih := @ih G x sp Δ Γ (a •[hd]) B' A (t •[hd]) B T wf (sorry) (sorry) h3
        sorry
      case all => sorry
      case arrow => sorry

      -- replace ih := @ih G x sp Δ Γ (a •[hd]) B' R (t •[hd]) B T wf (sorry) h2 h3 sorry
    case term hd =>
      -- have lem := Typing.inversion_apply_spine wf h3
      -- rcases lem with ⟨B', h1, h2, _, h3⟩
      -- apply ih wf

      -- have lem : StableTypeMatch Δ A (argA -:> R) := by apply StableTypeMatch.arrow; sorry
      -- have ih1 := ih
      sorry

    case oterm hd => sorry

-- apply @List.reverse_ind SpineElem
--   (λ ξ => ∀ G Δ Γ A R B T a t, ∀ x: String,  ∀ (sp : List SpineElem),
--     ⊢ G ->
--     a.spine = some (x, sp) ->
--     G&Δ,Γ ⊢ a : A ->
--     G&Δ,Γ ⊢ a.apply ξ : R ->
--     G&Δ,Γ ⊢ t : B ->
--     StableTypeMatch Δ A R ->
--     PrefixTypeMatch Δ A B T ->
--     G&Δ,Γ ⊢ t.apply ξ : T)
--   ξ
--   (by
--    intro G Δ Γ A R B T a t x sp wf h1 h2 h3 h4 h5 h6
--    simp [Term.apply] at *
--    have e := Typing.spine_term_unique_typing h2 h3 h1; cases e
--    have e := StableTypeMatch.prefix_type_match_forced_refl h5 h6; cases e
--    assumption)
--   (by
--     intro hd tl ih G Δ Γ A R B T a t x sp wf h1 h2 h3 h4 h5 h6
--     rw[Spine.apply_spine_compose] at h3; rw[Spine.apply_spine_compose]
--     cases hd
--     case type =>
--       cases h5 <;> simp [Term.apply] at *
--       case refl =>
--         cases h3; case _ h3 e =>
--         replace h3 := Typing.inversion_apply_spine wf h3
--         rcases h3 with ⟨w, j1, j2, _, j3⟩
--         have lem := Typing.spine_term_unique_typing h2 j2 h1; subst lem
--         sorry
--       case arrow => sorry
--       case all => sorry
--     case term =>
--       simp [Term.apply] at *
--       cases h3; case _ X q1 q2 q3 =>
--       replace h3 := Typing.inversion_apply_spine wf q3
--       rcases h3 with ⟨w, j1, j2, _, j3⟩
--       have lem := Typing.spine_term_unique_typing h2 j2 h1; subst lem
--       have lem : PrefixTypeMatch Δ (X -:> A) (X -:> B) T := by
--           apply PrefixTypeMatch.arrow; assumption
--       have lem' : StableTypeMatch Δ (X -:> A) R := by
--           apply StableTypeMatch.arrow; assumption

--       cases h5
--       case refl =>
--         apply Typing.app
--         apply q1
--         apply ih (A := A) (R := X -:> R) (B := B) (T := X -:> T)
--         · apply wf
--         · apply h1
--         · apply h2
--         · sorry
--         · apply h4
--         · sorry
--         · sorry

--         apply q2
--       case arrow =>
--         apply Typing.app
--         apply q1
--         sorry
--         apply q2
--       case all => sorry

--     case oterm => sorry



    -- case type hd =>

    --   sorry
    -- case term hd =>
    --   cases h3; case _ argA j1 j2 j3 =>
    --   have lem := Typing.inversion_apply_spine wf j3
    --   rcases lem with ⟨B', lem1, lem2, _, lem3⟩
    --   -- have lem : StableTypeMatch Δ A (argA -:> R) := by apply StableTypeMatch.arrow; sorry

    --   apply Typing.app
    --   apply j1
    --   sorry
    --   apply j2
    -- case oterm hd => sorry

  -- )
  -- G Δ Γ A R B T a t x sp wf h1 h2 h3 h4 h5 h6


theorem preservation_prefix_match {p s t : Term} :
  ⊢ G ->
  G&Δ,Γ ⊢ p : A ->
  G&Δ,Γ ⊢ s : R ->
  G&Δ,Γ ⊢ t : B ->
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  prefix_equal sp sp' = some ξ ->
  p.spine = some (x, sp) ->
  s.spine = some (x, sp') ->
  G&Δ,Γ ⊢ t.apply ξ : T
:= by
intro wf j1 j2 j3 j4 j5 j6 j7 j8
replace j6 := prefix_equal_law j6; subst j6
have h7 := Spine.apply_eq j7; subst h7
replace j8 := Spine.apply_eq j8; subst j8
rw [Spine.apply_spine_compose] at j2
apply preservation_prefix_match_lemma wf j7 j1 j2 j3 j4 j5
