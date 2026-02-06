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


theorem Typing.foldr_preservation_choiceₗ :
    G&Δ ⊢ B : .base b ->
    (∀ t ∈ is,  G&Δ, Γ ⊢ t : T) ->
    SpineType G Δ Γ sp B T ->
    G&Δ, Γ ⊢ List.foldr (λ t acc => t.apply sp `+ acc) `0 is : B := by
intro h1 h2 h3; induction is using List.foldr.induct <;> simp at *
case _ => apply Typing.zero; assumption
case _ i is ih =>
   rcases h2 with ⟨h2, h4⟩
   apply Typing.choice
   assumption
   apply SpineType.apply h2 h3
   apply ih h4




theorem preservation_prefix_match_lemma :
  a.spine = some (x, sp) ->
  G&Δ,Γ ⊢ a : A ->
  G&Δ,Γ ⊢ a.apply ξ : R ->
  G&Δ,Γ ⊢ t : B ->
  StableTypeMatch Δ A R ->
  PrefixTypeMatch Δ A B T ->
  G&Δ,Γ ⊢ t.apply ξ : T := by
intro h1 h2 h3 h4 h5 h6
induction ξ generalizing G Δ Γ A R B a t x sp <;> simp [Term.apply] at *
case _ =>
  have leme := Typing.spine_term_unique_typing h2 h3 h1; subst leme
  sorry
case _ => sorry



theorem preservation_prefix_match {p s t : Term} :
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
intro j1 j2 j3 j4 j5 j6 j7 j8
replace j6 := prefix_equal_law (Eq.symm j6); subst j6
have h7 := Spine.apply_eq j7; subst h7
replace j8 := Spine.apply_eq j8; subst j8
rw [Spine.apply_spine_compose] at j2
apply preservation_prefix_match_lemma j7 j1 j2 j3 j4 j5


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
    have lem' := GlobalWf.extract_kinding (Δ := Δ) (T := A) wf h1
    cases lem';
    apply Typing.foldr_preservation
    assumption
    apply lem
  case defn Δ _ Γ h1 _ _ _ _ _ h =>
    simp [Term.spine] at h; rcases h with ⟨e1, e2⟩; cases e1; cases e2;
    simp [Term.apply] at *
    case _ h =>
    have lem := lookup_defn_some h
    rcases lem with ⟨y, T, t, lem⟩
    simp [lookup_type] at h1; rw[lem] at h1; simp [Entry.type] at h1; cases h1
    simp [lookup_defn] at h; rw[lem] at h; simp at h; cases h
    apply lookup_defn_type_sound (Γ := Γ) (Δ := Δ) wf lem
case mtch =>
  cases h
  case data_match pats _ j1 vhv j2 h1 h2 h3 h4 h5 _ _ _ _ x _ _ i patshapes' patshapes h6 h7 h8 h9 h10 =>
    apply preservation_prefix_match
    apply (h2 i)
    apply j1
    apply h4 i
    apply h3 i
    apply h5 i
    apply (Eq.symm h8)
    · have lem2 := Vec.seq_sound h6
      replace lem2 := lem2 i
      have lem4 : (pats i).spine  = patshapes' i := by rw[h10]
      rw[lem4]; rw[lem2]
    · have lem3 := Vec.indexOf_correct (v := Vec.map (λ x => x.1) patshapes) (i := i) (x := x) h7;
      simp [Vec.map] at lem3; rw[lem3]; apply (Eq.symm h9)

  case data_match_default => assumption
  case match_congr ih _ _ _ _ h =>
    constructor; apply ih h; repeat assumption
  case match_absorb h _ _ _ _ _ _ _ _ _ _  =>
    replace h := Typing.well_typed_terms_have_base_kinds wf h
    cases h; apply Typing.zero; assumption
  case match_map j _ _ _ _ _ _ _ _ _ _ h ih =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j
    cases lem;
    cases h
    apply Typing.choice
    assumption
    · apply Typing.mtch; repeat assumption
    · apply Typing.mtch; repeat assumption
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
    apply (Eq.symm h8)
    apply (Eq.symm h9)
    apply (Eq.symm h10)

  case guard_missed j1 _ j2 _ _ _ h _ _ _ _ _ _ _ _ _ _ =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem1 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem2 =>
    have lem := PrefixTypeMatch.base_kinding lem1 lem2 h; cases lem
    apply Typing.zero; assumption
  case guard_congr ih _ _ h => constructor; assumption; apply ih h; repeat assumption
  case guard_absorb j1 j2 _ _ _ h _ _ _ _ =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem1 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem2 =>
    have lem := PrefixTypeMatch.base_kinding lem1 lem2 h; cases lem
    apply Typing.zero; assumption
  case guard_map j1 j2 _ _ _ j3 _ _ _ _ h _ =>
    cases h
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem1 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem2 =>
    have lem := PrefixTypeMatch.base_kinding lem1 lem2 j3; cases lem
    apply Typing.choice
    · assumption
    · constructor; repeat assumption
    · constructor; repeat assumption
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)

case app b _ f B a j1 j2 j3 ih1 ih2  =>
  cases h
  all_goals (try case _ h => simp at h)
  all_goals (try case _ h _ => simp at h)
  all_goals (try case _ h _ _ => simp at h)
  case beta =>
    cases j2; apply Typing.beta wf; assumption; assumption
  case inst Δ _ Γ x sp T _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    cases b
    case closed =>
      have lem := Typing.well_typed_terms_have_base_kinds wf j2
      cases lem; case _ lem =>
      cases lem; case _ j6 j7 =>
      have Tkj : ∃ bk, G&Δ ⊢ T : .base bk := GlobalWf.types_have_base_kind wf (Eq.symm h1)
      cases Tkj; case _ b Tkj =>
      have lem1 : G&Δ, Γ ⊢ g#x : T := by apply Typing.global; apply (Eq.symm h1); assumption
      have lem2 := @instance_type_preservation _ _ _ _ _ _ wf lem1 h3
      symm at h5; replace h5 := Spine.app_closed_eq.1 h5
      rcases h5 with ⟨sp', h6, h7⟩
      have h8 := Spine.apply_eq h7
      rw[h8] at j2
      have lem3 := Typing.inversion_apply_spine j2
      rcases lem3 with ⟨T', h9, h10, h11⟩
      have e := Typing.unique_var_typing lem1 h10; cases e
      have lem4 : SpineType G Δ Γ sp B T := by
        rw[h6]; apply SpineType.term
        apply j1; apply j3; (constructor; assumption; assumption)
        apply h9
      have lem5 := Typing.foldr_preservation_choiceₗ j7 lem2 lem4
      cases h3; cases h4; cases h6;
      rw[List.foldr_map]; apply lem5

    case «open» =>
      have lem := Typing.well_typed_terms_have_base_kinds wf j2
      cases lem; case _ lem =>
      cases lem; case _ j6 j7 =>
      have Tkj : ∃ bk, G&Δ ⊢ T : .base bk := GlobalWf.types_have_base_kind wf (Eq.symm h1)
      cases Tkj; case _ b Tkj =>
      have lem1 : G&Δ, Γ ⊢ g#x : T := by apply Typing.global; apply (Eq.symm h1); assumption
      have lem2 := @instance_type_preservation _ _ _ _ _ _ wf lem1 h3
      symm at h5; replace h5 := Spine.app_open_eq.1 h5
      rcases h5 with ⟨sp', h6, h7⟩
      have h8 := Spine.apply_eq h7
      rw[h8] at j2
      have lem3 := Typing.inversion_apply_spine j2
      rcases lem3 with ⟨T', h9, h10, h11⟩
      have e := Typing.unique_var_typing lem1 h10; cases e
      have lem4 : SpineType G Δ Γ sp B T := by
        rw[h6]; apply SpineType.oterm
        apply j1; apply j3; apply h9
      have lem5 := Typing.foldr_preservation_choiceₗ j7 lem2 lem4
      cases h3; cases h4; cases h6;
      rw[List.foldr_map]; apply lem5
  case defn Δ _ Γ x sp t h1 h2 =>
      have j3 := Typing.app j1 j2 j3
      have lem := Typing.well_typed_terms_have_base_kinds wf j2
      cases lem; case _ lem =>
      cases lem; case _ j6 j7 =>
      have lem1 := GlobalWf.lookup_defn_type (G := G) (Δ := Δ) (Γ := Γ) wf h1
      rcases lem1 with ⟨T, b, lem1, lem2, lem3⟩
      have h8 := Spine.apply_eq (Eq.symm h2)
      rw[h8] at j3
      have lem3 := Typing.inversion_apply_spine j3
      rcases lem3 with ⟨T', h9, h10, h11⟩
      have e := Typing.unique_var_typing lem1 h10; cases e
      apply SpineType.apply lem2 h9

  case ctor2_congr1 h =>
    apply Typing.app
    assumption
    apply ih1 h
    assumption
  case ctor2_congr2  h =>
    apply Typing.app; assumption; assumption; apply ih2 h
  case ctor2_absorb1 => cases j2; case _ j2 => cases j2; constructor; assumption
  case ctor2_absorb2 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem1 =>
    cases lem1;
    apply Typing.zero; assumption
  case ctor2_map1 =>
    cases j2; case _ j2 _ _ =>
    cases j2
    apply Typing.choice
    assumption
    · constructor; assumption; assumption; assumption
    · constructor; assumption; assumption; assumption
  case ctor2_map2 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem1 =>
    cases lem1;
    cases j3
    apply Typing.choice
    · assumption
    · constructor; assumption; assumption; assumption
    · constructor; assumption; assumption; assumption


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
  case inst Δ Γ K P P' e _ x sp T _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      have lem := Typing.well_typed_terms_have_base_kinds wf j1
      cases lem; case _ lem =>
      cases lem; case _ j6 j7 =>
      have Tkj : ∃ bk, G&Δ ⊢ T : .base bk := GlobalWf.types_have_base_kind wf (Eq.symm h1)
      cases Tkj; case _ b Tkj =>
      have lem1 : G&Δ, Γ ⊢ g#x : T := by apply Typing.global; apply (Eq.symm h1); assumption
      have lem2 := instance_type_preservation wf lem1 h3
      symm at h5; replace h5 := Spine.appt_eq.1 h5
      rcases h5 with ⟨sp', h6, h7⟩
      have h8 := Spine.apply_eq h7
      rw[h8] at j1
      have lem3 := Typing.inversion_apply_spine j1
      rcases lem3 with ⟨T', h9, h10, h11⟩
      have e := Typing.unique_var_typing lem1 h10; cases e
      have lem4 : SpineType G (K::Δ) (Γ.map (·[+1])) sp P' T := by
        rw[h6]; apply SpineType.type
        apply j2; (constructor; assumption); apply e
        apply h9
      -- have lem5 := Typing.foldr_preservation_choiceₗ (Kinding.all j7) lem2
      -- cases h3; cases h4; cases h6;
      -- rw[List.foldr_map]; apply lem5
      sorry
  case defn Δ _ Γ x sp t h1 h2 => sorry
  --     have j3 := Typing.app j1 j2 j3
  --     have lem := Typing.well_typed_terms_have_base_kinds wf j2
  --     cases lem; case _ lem =>
  --     cases lem; case _ j6 j7 =>
  --     have lem1 := GlobalWf.lookup_defn_type (G := G) (Δ := Δ) (Γ := Γ) wf h1
  --     rcases lem1 with ⟨T, b, lem1, lem2, lem3⟩
  --     have h8 := Spine.apply_eq (Eq.symm h2)
  --     rw[h8] at j3
  --     have lem3 := Typing.inversion_apply_spine j3
  --     rcases lem3 with ⟨T', h9, h10, h11⟩
  --     have e := Typing.unique_var_typing lem1 h10; cases e
  --     apply SpineType.apply lem2 h9
  case ctor1_congr ih _ h =>
    apply Typing.appt
    apply ih h
    assumption
    assumption
  case ctor1_absorb =>
    cases j1; case _ j1 =>
    cases j1; case _ e _ j1 =>
    have lem := Kinding.beta j1 j2
    rw[e]; constructor; assumption
  case ctor1_map =>
    cases j1
    case _ j _ _ =>
      cases j; case _  e _ _ _ _ _ _ _ _ j1 =>
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
    have lem := Typing.well_typed_terms_have_base_kinds wf tj
    cases lem; case _ lem =>
    cases cj; case _ cj =>
    cases cj; case _ cj _ =>
    have lem := Kinding.unique cj lem
    cases lem
    apply Typing.zero; assumption

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
    apply Typing.zero
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
    cases j2; case _ k1 k2 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1
    cases lem; case _ lem =>
    cases lem;
    apply Typing.zero
    apply Kinding.eq; assumption; assumption
  case ctor2_absorb2 j1 _ _ j2 _ =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1
    cases lem; case _ lem =>
    cases lem
    cases j2; case _ j2 =>
    cases j2;
    apply Typing.zero
    apply Kinding.eq; assumption; assumption
  case ctor2_map1 j1 _ _ _ _ _ j2 _  =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1
    cases lem; case _ lem =>
    cases lem
    cases j2; case _ j2 _ _ =>
    cases j2
    apply Typing.choice
    apply Kinding.eq; assumption; assumption
    apply Typing.seq; assumption; assumption
    apply Typing.seq; assumption; assumption
  case ctor2_map2 j1 _ _ _ _ _ j2 _ =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2;
    cases j2
    apply Typing.choice
    · apply Kinding.eq; assumption; assumption
    · apply Typing.seq; assumption; assumption
    · apply Typing.seq; assumption; assumption

case appc Δ Γ _ K1 K2 A B _ C D j1 j2 _ _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case appc =>
    cases j1; cases j2
    apply @Typing.refl G Δ (A • C) K2 Γ
    constructor; assumption; assumption
  case ctor2_congr1 ih _ _ _ h =>
    replace ih := ih h
    apply Typing.appc; assumption; assumption
  case ctor2_congr2 ih _ _ h =>
    replace ih := ih h
    apply Typing.appc; assumption; assumption

  case ctor2_absorb1 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2;
    apply Typing.zero
    · apply Kinding.eq
      · apply Kinding.app; assumption; assumption
      · apply Kinding.app; assumption; assumption
  case ctor2_absorb2 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2;
    apply Typing.zero
    · apply Kinding.eq
      · apply Kinding.app; assumption; assumption
      · apply Kinding.app; assumption; assumption
  case ctor2_map1 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2; cases j1
    apply Typing.choice
    · apply Kinding.eq;
      · apply Kinding.app; assumption; assumption
      · apply Kinding.app; assumption; assumption
    · apply Typing.appc; assumption; assumption
    · apply Typing.appc; assumption; assumption

  case ctor2_map2 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2; cases j2
    apply Typing.choice
    · apply Kinding.eq;
      · apply Kinding.app; assumption; assumption
      · apply Kinding.app; assumption; assumption
    · apply Typing.appc; assumption; assumption
    · apply Typing.appc; assumption; assumption



case arrowc j1 j2 _ _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case arrowc =>
    cases j1; cases j2;
    case _ j1 _ j2 _ =>
    have lem := Kinding.arrow j1 j2
    apply Typing.refl; apply lem;

  case ctor2_congr1 ih _ _ _ h =>
    replace ih := ih h
    constructor; assumption; assumption
  case ctor2_congr2 ih _ _ h =>
    replace ih := ih h
    constructor; assumption; assumption
  case ctor2_absorb1 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2;
    apply Typing.zero
    · apply Kinding.eq; repeat (apply Kinding.arrow; assumption; assumption)
  case ctor2_absorb2 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2;
    apply Typing.zero
    · apply Kinding.eq; repeat (apply Kinding.arrow; assumption; assumption)
  case ctor2_map1 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2; cases j1
    apply Typing.choice
    · apply Kinding.eq; repeat (apply Kinding.arrow; assumption; assumption)
    · apply Typing.arrowc; assumption; assumption
    · apply Typing.arrowc; assumption; assumption
  case ctor2_map2 =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j1; cases lem1; case _ lem1 =>
    cases lem1;
    have lem2 := Typing.well_typed_terms_have_base_kinds wf j2; cases lem2; case _ lem2 =>
    cases lem2; cases j2
    apply Typing.choice
    · apply Kinding.eq; repeat (apply Kinding.arrow; assumption; assumption)
    · apply Typing.arrowc; assumption; assumption
    · apply Typing.arrowc; assumption; assumption


case fst j1 j2 j3 ih  =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case fst =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j3; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    cases j1; cases j2; case _ j4 j5 _ j6 j7 =>
    have e := Kinding.unique j4 j1; cases e
    have e := Kinding.unique j6 j2; cases e
    cases j3; apply Typing.refl; assumption
  case ctor1_congr h =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j3; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    cases j1; cases j2; case _ j4 j5 _ j6 j7 =>
    have e := Kinding.unique j4 j1; cases e
    have e := Kinding.unique j6 j2; cases e
    have lem := ih h
    apply Typing.fst _ _ lem
    apply j4
    apply j6

  case ctor1_absorb =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j3; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    cases j1; cases j2; case _ j4 j5 _ j6 j7 =>
    have e := Kinding.unique j4 j1; cases e
    have e := Kinding.unique j6 j2; cases e
    apply Typing.zero
    apply Kinding.eq; assumption; assumption
  case ctor1_map =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j3; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    cases j1; cases j2; case _ j4 j5 _ j6 j7 =>
    have e := Kinding.unique j4 j1; cases e
    have e := Kinding.unique j6 j2; cases e
    cases j3; case _ j7 j8 =>
    apply Typing.choice
    · apply Kinding.eq; assumption; assumption
    · apply Typing.fst j4 j6 j7
    · apply Typing.fst j1 j2 j8

case snd j1 j2 j3 ih =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case snd => cases j3; apply Typing.refl; assumption
  case ctor1_congr h =>
    replace ih := ih h
    apply Typing.snd; repeat assumption

  case ctor1_absorb =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j3; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    cases j1; cases j2;
    case _ j4 j5 _ j6 j7 =>
    have e := Kinding.unique j4 j1; cases e
    have e := Kinding.unique j6 j2; cases e
    apply Typing.zero
    · apply Kinding.eq; repeat assumption
  case ctor1_map =>
    cases j3; case _ j3 j4 j5 =>
    apply Typing.choice
    · apply Kinding.eq; repeat assumption
    · apply Typing.snd; repeat assumption
    · apply Typing.snd; repeat assumption

case allc K Δ _ A B Γ j _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case allc B _ =>
    cases j; case _ b j _ =>
    apply Typing.refl
    apply Kinding.all; assumption
  case tbind_congr ih _ _ h =>
    replace ih := ih h
    apply Typing.allc; assumption
  case tbind_absorb ih =>
    have lem1 := Typing.well_typed_terms_have_base_kinds wf j; cases lem1; case _ lem1 =>
    cases lem1; case _ j1 j2 =>
    apply Typing.zero
    · apply Kinding.eq; repeat (apply Kinding.all; assumption)
  case tbind_map =>
    cases j; case _ j j1 j2 =>
    cases j; case _ j3 j4 =>
    apply Typing.choice
    · apply Kinding.eq; repeat (apply Kinding.all; assumption)
    · apply Typing.allc; assumption
    · apply Typing.allc; assumption

case apptc j1 j2 e1 e2 _  _ =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case apptc =>
    cases j1; cases j2
    rw[<-e1] at e2; subst e2; subst e1
    case _ j1 _ j2 _ =>
    cases j1; case _ j1 =>
    apply Typing.refl
    apply Kinding.beta j1 j2
  case ctor2_congr1 ih _ _ _ h =>
    replace ih := ih h
    subst e1; subst e2
    apply Typing.apptc
    assumption
    assumption
    rfl
    rfl
  case ctor2_congr2 _ ih _ _ h =>
    subst e1; subst e2
    apply Typing.apptc
    assumption
    apply ih h
    rfl
    rfl
  case ctor2_absorb1 =>
    subst e1; subst e2
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem =>
    cases lem; case _ j5 j6 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem =>
    cases lem; case _ j3 j4 =>
    cases j5; case _ j5 =>
    cases j6; case _ j6 =>
    apply Typing.zero
    · apply Kinding.eq
      apply Kinding.beta j5 j3
      apply Kinding.beta j6 j4
  case ctor2_absorb2 =>
    subst e1; subst e2
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem =>
    cases lem; case _ j3 j4 =>
    cases j3; case _ j3 =>
    cases j4; case _ j4 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem =>
    cases lem; case _ j5 j6 =>
    apply Typing.zero
    · apply Kinding.eq
      apply Kinding.beta j3 j5
      apply Kinding.beta j4 j6
  case ctor2_map1 =>
    subst e1; subst e2
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem =>
    cases lem; case _ j3 j4 =>
    cases j3; case _ j3 =>
    cases j4; case _ j4 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem =>
    cases lem; case _ j5 j6 =>
    cases j1;
    apply Typing.choice
    · apply Kinding.eq; apply Kinding.beta j3 j5; apply Kinding.beta j4 j6
    · apply Typing.apptc; assumption; assumption; rfl; rfl
    · apply Typing.apptc; assumption; assumption; rfl; rfl

  case ctor2_map2 =>
    subst e1; subst e2
    have lem := Typing.well_typed_terms_have_base_kinds wf j1; cases lem; case _ lem =>
    cases lem; case _ j3 j4 =>
    cases j3; case _ j3 =>
    cases j4; case _ j4 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2; cases lem; case _ lem =>
    cases lem; case _ j5 j6 =>
    cases j2
    apply Typing.choice
    · apply Kinding.eq; apply Kinding.beta j3 j5; apply Kinding.beta j4 j6
    · apply Typing.apptc; assumption; assumption; rfl; rfl
    · apply Typing.apptc; assumption; assumption; rfl; rfl
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
