import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Rename
import Core.Metatheory.Substitution
import Core.Metatheory.Uniqueness

theorem Kinding.invert_eq_kind : (G&Δ ⊢ (A ~[K]~ B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Kinding.invert_arr_kind : (G&Δ ⊢ (A -:> B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Kinding.inver_all_kind : (G&Δ ⊢ (∀[A] B) : w) -> w = ★ := by
intro j; cases j; simp

theorem Typing.lamt_unique : (G&Δ, Γ ⊢ (Λ[A] b) : t) -> (∃ B', t = ∀[A] B') := by
intros j; cases j; simp

theorem Typing.lam_unique : (G&Δ, Γ ⊢ λ[A]b : t) -> (∃ B', (t = (A -:> B'))) := by
intros j; cases j; simp

theorem Typing.lam_unique2 : (G&Δ, Γ ⊢ λ[A]b : (A' -:> B)) -> A = A' := by
intros j; cases j; simp

theorem Typing.refl_unique : (G&Δ, Γ ⊢ refl! A : T) -> ∃ K, (T = (A ~[K]~ A)) := by
intros j; cases j; simp


theorem PrefixTypeMatch.base_kinding :
  G&Δ ⊢ A : .base b1 ->
  G&Δ ⊢ B : .base b2 ->
  PrefixTypeMatch Δ A B T ->
  ∃ b, G&Δ ⊢ T : .base b := by
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
  cases ih; case _ b _ =>
  exists b;
  sorry -- requires strengthening


theorem ValidInstTy.base_kinded :
  ValidInstTy G x Δ T -> ∃ b, G&Δ ⊢ T : .base b := by
intro j; induction j <;> simp at *
exists b◯
exists b★; apply Kinding.all; assumption
case _ h =>
  rcases h with ⟨b, h⟩
  exists b★; apply Kinding.arrow; assumption
  apply h

theorem GlobalWf.extract_kinding :
  ⊢ G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢ T : .base b := by
intro wf h
induction G generalizing x T Δ
case _ => simp [lookup_type, lookup] at *
case _ hd tl ih =>
  cases wf; case _ wftl wfh =>
  induction wfh
  sorry
  sorry
  sorry
  sorry
  sorry
  case _ y G T h1 h2 =>
    simp [lookup_type, lookup] at h
    split at h
    case _ e =>
      subst e
      simp [Entry.type] at h; cases h
      have lem := ValidInstTy.base_kinded h2
      cases lem; case _ b lem =>
      exists b;
      sorry
    sorry


theorem Typing.well_typed_terms_have_base_kinds :
  ⊢ G ->
  G&Δ, Γ ⊢ t : A -> ∃ b, G&Δ ⊢ A : .base b := by
intro wf j; induction j
case _ => sorry
case _ h => apply GlobalWf.extract_kinding wf; assumption
case _ => assumption
case _ h1 h2 _ h3 =>
  cases h2; case _ h2 =>
  cases h3; case _ h3 =>
  apply PrefixTypeMatch.base_kinding h2 h3 h1
case _ h =>
  rcases h with ⟨_, h⟩
  exists b★; constructor; assumption; assumption
case _ h _ =>
  rcases h with ⟨_, h⟩
  cases h; case _ b _ _  =>
  exists b
case _ => exists b★
case _ h =>
  rcases h with ⟨b, h⟩
  cases h; case _ h1 e h2 =>
  exists b★;
  subst e;
  apply Kinding.beta h2 h1
case _ h3 h1 =>
  cases h1; case _ h1 =>
  cases h1; case _ h1 h2 =>
  cases h3; case _ w h3 =>
  exists w
  have lem := Kinding.unique h1 h3; cases lem
  assumption
case _ => exists b★; apply Kinding.eq; assumption; assumption
case _ h =>
  cases h; case _ h =>
  cases h; exists b★
  apply Kinding.eq; assumption; assumption
case _ h1 h2 =>
  exists b★
  cases h1; case _ h1 =>
  cases h1; cases h2; case _ h2 =>
  cases h2
  apply Kinding.eq; assumption; assumption
case _ h1 h2 =>
  cases h1; case _ h1 =>
  cases h1; cases h2; case _ h2 =>
  cases h2
  exists b★
  apply Kinding.eq
  · apply Kinding.app; assumption; assumption
  · apply Kinding.app; assumption; assumption
case _ h1 h2 =>
  cases h1; case _ h1 =>
  cases h1; cases h2; case _ h2 =>
  cases h2
  exists b★
  apply Kinding.eq
  · apply Kinding.arrow; assumption; assumption
  · apply Kinding.arrow; assumption; assumption
case _ h =>
  cases h; case _ h =>
  cases h; case _ h1 h2 =>
  cases h1; cases h2
  case _ h1 h3 _ _ h2 _ _ h4 _ =>
  have lem := Kinding.unique h1 h2; cases lem
  have lem := Kinding.unique h3 h4; cases lem
  exists b★
  apply Kinding.eq; assumption; assumption
case _ h =>
  cases h; case _ h =>
  cases h; case _ h1 h2 =>
  cases h1; cases h2;
  case _ h1 h3 _ _ h2 _ _ h4 _ =>
  have lem := Kinding.unique h1 h2; cases lem
  have lem := Kinding.unique h3 h4; cases lem
  exists b★
  apply Kinding.eq; assumption; assumption
case _ h =>
  cases h; case _ h =>
  cases h;
  exists b★
  apply Kinding.eq
  · apply Kinding.all; assumption
  · apply Kinding.all; assumption
case _ e1 e2 h1 h2 =>
  cases h1; case _ h1 =>
  cases h1; case _ h1 h2 =>
  cases h1; cases h2
  cases h2; case _ h2 =>
  cases h2; case _ h1 h2 h3 h4 =>
  exists b★
  subst e1; subst e2
  apply Kinding.eq
  · apply Kinding.beta h1 h3
  · apply Kinding.beta h2 h4
case _ b _ _ => exists b
case _ => assumption



theorem Typing.inversion_apply_spine :
  ⊢ G ->
  G&Δ,Γ ⊢ t.apply sp : A ->
  ∃ B, SpineType G Δ Γ sp A B ∧ G&Δ, Γ ⊢ t : B ∧ (∃ b, G&Δ ⊢ B : .base b) := by
intro wf j
apply @List.reverse_ind SpineElem
   (λ x => ∀ G Δ Γ t A, ⊢ G -> G&Δ,Γ ⊢ t.apply x : A ->
      ∃ B, SpineType G Δ Γ x A B ∧ G&Δ, Γ ⊢ t : B ∧ (∃ b, G&Δ ⊢ B : .base b))
   sp
   (by
     intro G Δ Γ t A wf j
     exists A
     simp [Term.apply] at j
     constructor
     · apply SpineType.refl
     · constructor
       assumption; intros; apply well_typed_terms_have_base_kinds wf j )
   (by intro hd tl ih G Δ Γ t A wf j2
       have lem := well_typed_terms_have_base_kinds wf j2
       rcases lem with ⟨Abk, lem⟩
       rw[Spine.apply_spine_compose] at j2
       cases hd
       all_goals (
          simp [Term.apply] at j2
       )
       case type a K P j1 j2 a =>
         cases j2; case _ K P jk j2 e =>
         replace ih := ih G Δ Γ t (∀[K]P) wf j2
         rcases ih with ⟨B, h1, h2, h3⟩
         exists B
         constructor
         · apply SpineType.type (P := P) jk;
           have lem := well_typed_terms_have_base_kinds wf j2
           rcases lem with ⟨b, lem⟩
           have e := Kinding.inver_all_kind lem; cases e
           assumption; apply e; assumption
         · constructor; assumption; assumption
       case term x T a arg =>
         cases j2
         case _ X jk j1 j2 =>
         replace ih1 := ih G Δ Γ t (X -:> A) wf j2
         rcases ih1 with ⟨B, h1, h2, h3⟩
         exists B
         constructor;
         · apply SpineType.term jk j1;
           · constructor; assumption; apply lem
           apply h1
         · constructor;
           assumption; assumption
       case oterm x T a arg j2 =>
         cases j2
         case _ X jk j1 j2 =>
         replace ih1 := ih G Δ Γ t (X -:> A) wf j2
         rcases ih1 with ⟨B, h1, h2, h3⟩
         exists B
         constructor;
         · apply SpineType.oterm jk j1 h1
         · constructor; assumption; assumption
   )
   G Δ Γ t A wf j
