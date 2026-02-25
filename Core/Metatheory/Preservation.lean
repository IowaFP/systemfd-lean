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
import Core.Metatheory.Preservation.Lemmas

open LeanSubst

namespace Core

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
    case _ x A Δ K Γ h1 h2 _ tl _ _ is _ _ e =>
    have lem : G&Δ, Γ ⊢ g#x : A := by constructor; apply h1; apply h2
    replace lem := instance_type_preservation wf lem is
    cases is; case _ e =>
    cases e
    have lem' := GlobalWf.types_have_base_kind (Δ := Δ) (T := A) wf h1
    cases lem'; case _ _ h =>
    replace lem := fix_quantifiers (Δ := Δ) (Γ := Γ) lem
    apply Typing.foldr_preservation
    assumption
    intro t h
    apply lem t h
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
  case data_match pats _ j1 vhv j2 h1 h2 h3 h4 h5 _ _ _ _ x _ _ i patshapes' patshapes cns h6 h7 h8 h9 h10 h11 =>
    apply preservation_prefix_match wf
    apply (h2 i)
    apply j1
    apply h4 i
    apply h3 i
    apply h5 i
    apply (Eq.symm h9)
    · have lem2 := Vect.seq_sound h6
      replace lem2 := lem2 i
      have lem4 : (pats i).spine = patshapes' i := by rw[h11]
      rw[lem4]; rw[lem2]
    · have lem3 := Vect.indexOf_correct (v := cns) (i := i) (x := x) h8;
      have lem4 : (patshapes i).fst = cns i := by rw[h7]
      rw[lem4, lem3]; apply (Eq.symm h10)

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
    apply preservation_prefix_match wf
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
  case inst Δ _ Γ x sp T _ _ _ h1 h2 h3 h4 h5 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j2
    rcases lem with ⟨bk, lem⟩
    cases lem; case _ lemj1 lemj2 =>
    have e := Kinding.unique j1 lemj1; cases e
    have Tkj : ∃ bk, G&Δ ⊢ T : .base bk := GlobalWf.types_have_base_kind wf (Eq.symm h1)
    cases Tkj; case _ bk Tkj =>
    have lem1 : G&Δ, Γ ⊢ g#x : T := by apply Typing.global; apply (Eq.symm h1); assumption
    have lem2 := instance_type_preservation wf lem1 h3
    replace lem2 := fix_quantifiers (Δ := Δ) (Γ := Γ) lem2
    have zero_typing : G&Δ, Γ ⊢ `0 : T := by apply Typing.zero; assumption

    have lem := Typing.foldr_preservation_choiceₗ Tkj zero_typing lem2
    cases b
    case _ =>
      have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
      have j4 := Typing.app j1 j2 j3
      have lem2 := Spine.app_closed_eq.1 (Eq.symm h4)
      rcases lem2 with  ⟨sp', e, lem2⟩
      replace h4 := Spine.apply_eq (Eq.symm h4); rw[h4] at j4

      have lem := Typing.replace_head_regular wf xnf lem1 lem j4
      cases h3; cases h5
      apply lem
    case _ =>
    case _ =>
      have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
      have j4 := Typing.app j1 j2 j3
      have lem2 := Spine.app_open_eq.1 (Eq.symm h4)
      rcases lem2 with  ⟨sp', e, lem2⟩
      replace h4 := Spine.apply_eq (Eq.symm h4); rw[h4] at j4

      have lem := Typing.replace_head_regular wf xnf lem1 lem j4
      cases h3; cases h5
      apply lem
  case defn Δ _ Γ x sp t h1 h2 =>
      have j4 := Typing.app j1 j2 j3
      have lem := Typing.well_typed_terms_have_base_kinds wf j2
      cases lem; case _ lem =>
      cases lem; case _ j6 j7 =>
      have lem1 := GlobalWf.lookup_defn_type (G := G) (Δ := Δ) (Γ := Γ) wf h1
      rcases lem1 with ⟨T,_, lem1, lem2, lem3⟩
      have h8 := Spine.apply_eq (Eq.symm h2)
      rw[h8] at j4
      cases b
      case _ =>
         have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
         replace h4 := Spine.apply_eq (Eq.symm h2);
         have lem := Typing.replace_head_regular wf xnf lem1 lem2 j4
         apply lem
      case _ =>
         have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
         replace h4 := Spine.apply_eq (Eq.symm h2);
         have lem := Typing.replace_head_regular wf xnf lem1 lem2 j4
         apply lem
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
  case inst Δ Γ K P P' e _ x sp T _ _ _ h1 h2 h3 h4 h5 =>
    have lem := Typing.well_typed_terms_have_base_kinds wf j1
    rcases lem with ⟨bk, lem⟩
    cases lem; case _ lemj1 =>
    have Tkj : ∃ bk, G&Δ ⊢ T : .base bk := GlobalWf.types_have_base_kind wf (Eq.symm h1)
    cases Tkj; case _ b Tkj =>
    have lem1 : G&Δ, Γ ⊢ g#x : T := by apply Typing.global; apply (Eq.symm h1); assumption
    have lem2 := instance_type_preservation wf lem1 h3
    replace lem2 := fix_quantifiers (Δ := Δ) (Γ := Γ) lem2
    have zero_typing : G&Δ, Γ ⊢ `0 : T := by apply Typing.zero; assumption

    have lem := Typing.foldr_preservation_choiceₗ Tkj zero_typing lem2
    have app_ty := Typing.appt j1 j2 e
    have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
    replace h4 := Spine.apply_eq (Eq.symm h4); rw[h4] at app_ty
    have lem := Typing.replace_head_regular wf xnf lem1 lem app_ty
    cases h5
    apply lem
  case defn Δ Γ _ _ _ e _ x sp t h1 h2 =>
      have j3 := Typing.appt j1 j2 e
      have lem := Typing.well_typed_terms_have_base_kinds wf j3
      cases lem; case _ b j7 =>
      have lem1 := GlobalWf.lookup_defn_type (G := G) (Δ := Δ) (Γ := Γ) wf h1
      rcases lem1 with ⟨T, b, lem1, lem2, lem3⟩
      have h8 := Spine.apply_eq (Eq.symm h2)
      rw[h8] at j3
      have app_ty := Typing.appt j1 j2 e
      have xnf : (g#x).spine = .some (x, []) := by simp [Term.spine]
      have lem := Typing.replace_head_regular wf xnf lem1 lem2 j3
      apply lem

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

end Core
