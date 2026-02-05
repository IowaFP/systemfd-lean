import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Metatheory.GlobalWf

open LeanSubst

theorem instance_type_preservation :
  ⊢ G ->
  G&Δ, Γ ⊢ g#x : T ->
  is = instances x G ->
  ∀ t ∈ is, G&Δ, Γ ⊢ t : T := by
intro wf j h t t_in_is
sorry

theorem lookup_defn_type_sound :
  ⊢ G ->
  lookup x G = .some (Entry.defn y T t) ->
  G&[],[] ⊢ t : T := by
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
    sorry

theorem Typing.foldr_preservation :
  G&Δ ⊢ T : K ->
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


theorem preservation_prefix_match {p s t : Term} :
  G&Δ,Γ ⊢ p : A ->
  G&Δ,Γ ⊢ s : R ->
  G&Δ,Γ ⊢ t : B ->
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  some ξ = prefix_equal sp sp' ->
  some (x, sp) = p.spine ->
  some (x, sp') = s.spine ->
  G&Δ,Γ ⊢ t.apply ξ : T
:= by
intro j1 j2 j3 j4 j5 j6 j7 j8
replace j6 := prefix_equal_law j6; subst j6
have h7 := Term.apply_eq j7; subst h7
replace j8 := Term.neutral_form_law j8; subst j8
rw [Term.apply_spine_compose] at j2
apply preservation_prefix_match_lemma (Eq.symm j7) j1 j2 j3 j4 j5

-- induction s using Term.spine.induct generalizing x sp sp'
-- case _ =>
--   simp [Term.spine] at j8; rcases j8 with ⟨j8, j9⟩
--   cases j8; cases j9
--   induction p using Term.spine.induct
--   case _ =>
--     simp [Term.spine] at j7; rcases j7 with ⟨j8, j9⟩
--     cases j8; cases j9
--     simp [prefix_equal] at j6; cases j6
--     simp [Term.apply]
--     cases j1; cases j2; case _ j1 _ _ j2 => rw[j1] at j2; cases j2; sorry
--   simp [Term.spine] at j7; symm at j7
--   rw[Option.bind_eq_some_iff] at j7; rcases j7 with ⟨_, j7, j8⟩
--   sorry
--   sorry
--   sorry
--   sorry
-- sorry
-- sorry
-- sorry
-- sorry


theorem preservation_lemma :
  ⊢ G ->
  G&Δ, Γ ⊢ t : T ->
  G ⊢ t ~> t' ->
  G&Δ, Γ ⊢ t' : T  := by
intro wf j h
induction j generalizing t' <;> simp at *
case var h' _ =>
  cases h
  case _ h _ => simp [Term.spine] at h
  case _ h => simp [Term.spine] at h
all_goals (try simp at *)
case global =>
  cases h
  case inst h _ =>
    simp [Term.spine] at h; rcases h with ⟨e1, e2⟩; cases e1; cases e2;
    simp [Term.apply] at *
    case _ x A Δ K Γ h1 h2 _ tl _ _ _ _ is _ _ e =>
    cases e
    have lem : G&Δ, Γ ⊢ g#x : A := by constructor; apply h1; apply h2
    replace lem := instance_type_preservation wf lem is
    cases is; case _ e =>
    cases e
    apply Typing.foldr_preservation
    apply h2
    apply lem
  case defn h =>
    simp [Term.spine] at h; rcases h with ⟨e1, e2⟩; cases e1; cases e2;
    simp [Term.apply] at *
    sorry -- apply lookup_defn_type_sound wf; assumption

case mtch =>
  cases h
  case data_match pats _ j1 vhv j2 h1 h2 h3 h4 h5 _ _ _ _ x _ _ i patshapes' patshapes h6 h7 h8 h9 h10 =>
    apply preservation_prefix_match
    apply (h2 i)
    apply j1
    apply h4 i
    apply h3 i
    apply h5 i
    apply h8
    · have lem2 := Vec.seq_sound h6
      replace lem2 := lem2 i
      have lem4 : (pats i).spine  = patshapes' i := by rw[h10]
      rw[lem4]; rw[lem2]
    · have lem3 := Vec.indexOf_correct (v := Vec.map (λ x => x.1) patshapes) (i := i) (x := x) h7;
      simp [Vec.map] at lem3; rw[lem3]; assumption

  case data_match_default =>  assumption

  case match_congr ih _ _ _ _ h =>
    constructor
    apply ih h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption

  case match_absorb =>
    -- need to show T is of base type
    sorry
  case match_map h ih =>
    cases h
    apply Typing.choice
    sorry -- need to show T is of base type
    · apply Typing.mtch; assumption; assumption; assumption; assumption; assumption; assumption; assumption; assumption
    · apply Typing.mtch; assumption; assumption; assumption; assumption; assumption; assumption; assumption; assumption
    sorry
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)

case guard =>
  cases h
  case guard_matched h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ _ _ h8 h9 h10 =>
    apply preservation_prefix_match
    apply h1
    apply h2
    apply h3
    apply h6
    apply h7
    apply h8
    apply h9
    apply h10

  case guard_missed =>
    sorry -- need to show T is of base type
  case guard_congr ih _ _ h =>
    constructor; assumption; apply ih h; assumption; assumption; assumption; assumption; assumption
  case guard_absorb =>
    sorry  -- need to show T is of base type
  case guard_map h _ =>
    cases h
    apply Typing.choice
    sorry -- T is of base type
    · constructor; assumption; assumption; assumption; assumption; assumption; assumption; assumption
    · constructor; assumption; assumption; assumption; assumption; assumption; assumption; assumption
    sorry
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)

case app b _ f _ a j1 j2 j3 _ _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp at h)
  all_goals (try case _ h _ _ => simp at h)
  case beta =>
    cases j2; apply Typing.beta wf; assumption; assumption
  case inst => sorry
  case defn t h1 h2 =>

    sorry
  case ctor2_congr1 ih _ _ _ h =>
    apply Typing.app
    assumption
    apply ih h
    assumption
  case ctor2_congr2 ih _ _ h =>
    apply Typing.app; assumption; assumption; apply ih h
  case ctor2_absorb1 => cases j2; case _ j2 => cases j2; constructor; assumption
  case ctor2_absorb2 => sorry
  case ctor2_map1 =>
    cases j2; case _ j2 _ _ =>
    cases j2
    apply Typing.choice
    assumption
    · constructor; assumption; assumption; assumption
    · constructor; assumption; assumption; assumption
  case ctor2_map2 =>
    cases j3
    apply Typing.choice
    sorry
    · constructor; assumption; assumption; assumption
    · constructor; assumption; assumption; assumption
    sorry

case appt f _ _ a _ j1 j2 _ _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp at h)
  all_goals (try case _ h _ _ => simp at h)
  case betat Δ Γ K P _ e A b _ =>
    cases j1; case _ j1 =>
    rw[e];
    have lem := @Typing.beta_type G K Δ (Γ.map (λ x => x[+1])) b P a wf j1 j2
    simp at lem
    have lem2 : List.map ((λ x => x[su a::+0]) ∘ (λ x => x[+1])) Γ = Γ := by
      generalize fdef : (λ x => x[su a::+0]) ∘ (λ x => x[+1]) = f at *
      simp [Function.comp_def] at fdef
      rw[<-fdef]; simp
    rw[lem2] at lem
    assumption
  case inst => sorry
  case defn => sorry
  case ctor1_congr ih _ h =>
    apply Typing.appt
    apply ih h
    assumption
    assumption
  case ctor1_absorb =>
    cases j1; case _ j1 =>
    cases j1; case _ e _ _ j1 =>
    have lem := Kinding.beta j1 j2
    rw[e]; constructor; assumption
  case ctor1_map =>
    cases j1
    case _ j _ _ =>
      cases j; case _ e _ _ _ _ _ _ _ _ _ j1 =>
      rw[e]
      apply Typing.choice
      apply Kinding.beta j1 j2
      · apply Typing.appt; assumption; assumption; simp
      · apply Typing.appt; assumption; assumption; simp

case lam =>
  cases h
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
case lamt =>
  cases h
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
  case _ h _ => simp at h
  all_goals (case _ h _ _ => simp at h)

case cast tj cj _ ih =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case _ => cases cj; assumption
  case _ t _ c _ _ _ t' h cr =>
    simp at *; replace ih := ih cr
    constructor; assumption; assumption
  case _ =>
    cases cj; case _ cj =>
    cases cj; constructor; assumption
  case _ =>
    cases cj; case _ cj _ _ =>
    cases cj;
    apply Typing.choice
    assumption
    constructor; assumption; assumption
    constructor; assumption; assumption

case refl =>
  cases h
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
case sym =>
  cases h;
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)

  case _ h _ => cases h; constructor; assumption
  case _ ih t' r => replace ih := ih r; constructor; assumption
  case _ j _ =>
    cases j; case _ j =>
    cases j; case _ K _ _ _ _ _ =>
    apply Typing.zero (K := ★)
    constructor; assumption; assumption
  case _ j ih =>
    cases j; case _ j _ _ =>
    cases j
    apply Typing.choice
    constructor; assumption; assumption
    constructor; assumption
    constructor; assumption
case seq =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case seq j1 _ j2 _  => cases j1; cases j2; constructor; assumption
  case ctor2_congr1 ih _ _ _ h =>
    constructor
    apply ih h
    assumption
  case ctor2_congr2 ih _ _ h =>
    constructor
    assumption
    apply ih h
  case ctor2_absorb1 j1 _ _ j2 _ =>
    cases j2; case _ j2 =>
    cases j2;
    -- need some nice properties from wf contexts
    sorry
  case ctor2_absorb2 =>

    sorry
  case ctor2_map1 j1 _ _ _ _ _ j2 _  =>
    cases j2; case _ j2 _ _ =>
    cases j2
    apply Typing.choice
    constructor;
    · assumption
    · sorry
    constructor
    assumption
    assumption
    constructor; assumption; assumption

  case ctor2_map2 =>
    sorry
case appc Δ Γ _ K1 K2 A B _ C D _ _ _ _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case appc j1 _ j2 _ =>
    cases j1; cases j2
    apply @Typing.refl G Δ (A • C) K2 Γ
    constructor; assumption; assumption

  case ctor2_congr1 => sorry
  case ctor2_congr2 => sorry
  case ctor2_absorb1 => sorry
  case ctor2_absorb2 => sorry
  case ctor2_map1 => sorry
  case ctor2_map2 => sorry

case arrowc =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case arrowc => sorry

  case ctor2_congr1 => sorry
  case ctor2_congr2 => sorry
  case ctor2_absorb1 => sorry
  case ctor2_absorb2 => sorry
  case ctor2_map1 => sorry
  case ctor2_map2 => sorry

case fst =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case fst => sorry
  case ctor1_congr => sorry
  case ctor1_absorb => sorry
  case ctor1_map => sorry

case snd =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case snd => sorry
  case ctor1_congr => sorry
  case ctor1_absorb => sorry
  case ctor1_map => sorry

case allc K Δ _ _ A B Γ j _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case allc B _ =>
    cases j; case _ b j _ =>
    apply @Typing.refl G Δ (∀[K]A) ★ Γ (Kinding.all j)
  case tbind_congr => sorry
  case tbind_absorb => sorry
  case tbind_map => sorry

case apptc =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case apptc e1 e2 _ _ _ h1 _ h2 _ =>
    cases h1; cases h2
    rw[<-e1] at e2; subst e2; subst e1
    constructor; case _ j1 _ j2 _ =>
    cases j1; case _ j1 =>
    have lem := Kinding.beta j1 j2
    sorry

  case ctor2_congr1 => sorry
  case ctor2_congr2 => sorry
  case ctor2_absorb1 => sorry
  case ctor2_absorb2 => sorry
  case ctor2_map1 => sorry
  case ctor2_map2 => sorry

case zero =>
  cases h;
  case _ h _ => cases h
  all_goals (try case _ h => simp [Term.spine] at h)

case choice =>
  cases h
  all_goals (try assumption)
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  case _ ih _ _ _ r =>
    replace ih := ih r
    apply Typing.choice; assumption; assumption; assumption
  case _ ih _ _ r =>
    replace ih := ih r
    apply Typing.choice; assumption; assumption; assumption
  all_goals (case _ h _ _ => simp at h)
