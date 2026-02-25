import LeanSubst
import Lilac

import Core.Typing
import Core.Util
import Core.Metatheory.FreeVars
import Core.Metatheory.Rename

open LeanSubst

namespace Core

theorem PrefixTypeMatch.closed_rep σ :
  A[rep Subst.lift σ Δ.length] = A ->
  B[rep Subst.lift σ Δ.length] = B ->
  PrefixTypeMatch Δ A B T ->
  T[rep Subst.lift σ Δ.length] = T
:= by
  intro h1 h2 j
  induction j generalizing σ
  case refl => exact h2
  case arrow ih =>
    simp at ih h1 h2
    apply ih σ h1.2 h2.2
  case all Δ _ _ T _ ih =>
    simp at ih h1 h2
    have lem := ih σ h1 h2
    have lem2 : T[rep Subst.lift σ Δ.length ∘ +1:Ty][-1:Ty] = T[+1:Ty][-1:Ty] := by rw [lem]
    simp at lem2; exact lem2

theorem Typing.closed_type_rep :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[rep Subst.lift σ Δ.length:Ty] = t ∧ A[rep Subst.lift σ Δ.length:_] = A
:= by
  intro j; induction j <;> intro σ
  case var j1 j2 => simp; apply Kinding.closed_rep j2
  case global j1 j2 => simp; apply Kinding.closed_rep j2
  case mtch j1 j2 j3 j4 j5 j6 j7 j8 ih1 ih2 ih3 ih4 =>
    have lem1 := λ i => (ih3 i σ).1
    have lem4 := λ i => (ih4 i σ).1
    simp; simp at lem1
    exact ⟨⟨(ih1 σ).1, (by funext; apply lem1), (by funext; apply lem4), (ih2 σ).1⟩, (ih2 σ).2⟩
  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    simp
    obtain ⟨q1, q2⟩ := ih1 σ
    obtain ⟨q3, q4⟩ := ih2 σ
    obtain ⟨q5, q6⟩ := ih3 σ
    have lem := PrefixTypeMatch.closed_rep σ q2 q6 j7
    exact ⟨⟨q1, q3, q5⟩, lem⟩
  case lam j1 j2 ih =>
    have lem := Kinding.closed_rep j1 σ
    obtain ⟨ih1, ih2⟩ := ih σ
    simp; exact ⟨⟨lem, ih1⟩, ⟨lem, ih2⟩⟩
  case app ih1 ih2 =>
    simp at ih1 ih2; simp
    obtain ⟨q1, q2, q3⟩ := ih1 σ
    exact ⟨⟨q1, (ih2 σ).1⟩, q3⟩
  case lamt ih =>
    simp at ih; simp
    apply ih σ
  case appt j1 j2 j3 ih =>
    have lem := Kinding.closed_rep j2 σ
    obtain ⟨ih1, ih2⟩ := ih σ
    simp at ih1 ih2; simp
    apply And.intro ⟨lem, ih1⟩
    subst j3
    conv => rhs; rw [<-ih2]; simp
    simp; rw [lem]
  case cast ih1 ih2 =>
    simp at ih2; simp
    obtain ⟨q1, q2⟩ := ih1 σ
    obtain ⟨q3, q4, q5⟩ := ih2 σ
    exact ⟨⟨q1, q3⟩, q5⟩
  case refl j =>
    simp; apply Kinding.closed_rep j
  case sym j ih =>
    simp at ih; simp
    obtain ⟨q1, q2, q3⟩ := ih σ
    exact ⟨q1, q3, q2⟩
  case seq ih1 ih2 =>
    simp at ih1 ih2; simp
    obtain ⟨q1, q2, q3⟩ := ih1 σ
    obtain ⟨q4, q5, q6⟩ := ih2 σ
    exact ⟨⟨q1, q4⟩, q2, q6⟩
  case appc ih1 ih2 =>
    simp at ih1 ih2; simp
    obtain ⟨q1, q2, q3⟩ := ih1 σ
    obtain ⟨q4, q5, q6⟩ := ih2 σ
    exact ⟨⟨q1, q4⟩, ⟨q2, q5⟩, q3, q6⟩
  case arrowc ih1 ih2 =>
    simp at ih1 ih2; simp
    obtain ⟨q1, q2, q3⟩ := ih1 σ
    obtain ⟨q4, q5, q6⟩ := ih2 σ
    exact ⟨⟨q1, q4⟩, ⟨q2, q5⟩, q3, q6⟩
  case fst ih =>
    simp at ih; simp
    obtain ⟨q1, ⟨q2, q3⟩, q4, q5⟩ := ih σ
    exact ⟨q1, q2, q4⟩
  case snd ih =>
    simp at ih; simp
    obtain ⟨q1, ⟨q2, q3⟩, q4, q5⟩ := ih σ
    exact ⟨q1, q3, q5⟩
  case allc ih =>
    simp at ih; simp
    apply ih σ
  case apptc j1 j2 ih1 ih2 =>
    simp at ih1 ih2; simp
    obtain ⟨q1, q2, q3⟩ := ih1 σ
    obtain ⟨q4, q5, q6⟩ := ih2 σ
    apply And.intro ⟨q1, q4⟩
    apply And.intro
    subst j1; conv => rhs; rw [<-q2]; simp
    simp; rw [q5]
    subst j2; conv => rhs; rw [<-q3]; simp
    simp; rw [q6]
  case zero j =>
    simp; apply Kinding.closed_rep j
  case choice ih1 ih2 =>
    simp
    obtain ⟨q1, q2⟩ := ih1 σ
    obtain ⟨q3, q4⟩ := ih2 σ
    exact ⟨⟨q1, q3⟩, q4⟩

theorem Typing.closed_type :
  G&[],Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[σ:Ty] = t ∧ A[σ:_] = A
:= by
  intro j σ
  have lem := closed_type_rep j σ; simp at lem
  exact lem

theorem Typing.closed_rep :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[rep Subst.lift σ Γ.length ◾ τ:_] = t
:= by
  intro j; induction j <;> intro σ τ
  all_goals try solve | simp; try grind
  case var Γ x A Δ b j1 j2 =>
    have lem : x < Γ.length := Γ.indexing_length_some j1
    simp; rw [subst_lift σ lem]; simp
  case mtch ih1 ih2 ih3 ih4 =>
    simp
    exact ⟨ih1 _ _, (by funext; apply ih3 _ _ _), (by funext; apply ih4 _ _ _), ih2 _ _⟩
  case lam j1 j2 ih =>
    replace ih := ih σ τ; simp at ih; simp
    exact ih

theorem Typing.closed :
  G&Δ,[] ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[σ ◾ τ:_] = t
:= by
  intro j σ
  have lem := closed_rep j σ; simp at lem
  exact lem

theorem Typing.weaken_type_closed Δ :
  ⊢ G ->
  G&[],[] ⊢ t : A ->
  G&Δ,[] ⊢ t : A
:= by
  intro wf j
  have lem1 := weaken_type_list Δ wf j; simp at lem1
  obtain ⟨q1, q2⟩ := closed_type j (Ren.to (· + Δ.length))
  rw [q1, q2] at lem1
  exact lem1

theorem Typing.weaken_closed Γ :
  ⊢ G ->
  G&Δ,[] ⊢ t : A ->
  G&Δ,Γ ⊢ t : A
:= by
  intro wf j
  have lem1 := weaken_list Γ wf j; simp at lem1
  have lem2 := closed j (Ren.to (· + Γ.length)) +0; simp at lem2
  rw [lem2] at lem1
  exact lem1

theorem Kinding.closed_lifting_lemma : ∀ Δ', ⊢ G ->  G&Δ ⊢ T : K -> (G&(Δ' ++ Δ) ⊢ T[Ren.to (λ x => (x + Δ'.length))] : K) := by
intro Δ' wf j
apply @List.reverse_ind (T := Kind)
  (motive := λ Δ' => ∀ G Δ T K,  ⊢ G -> G&Δ ⊢ T : K -> (G&(Δ' ++ Δ) ⊢ T[Ren.to (λ x => (x + Δ'.length))] : K))
  Δ'
  (by intro G Δ T K wf j;
      have lem : (Ren.to (λ x => x)) = Subst.id (T := Ty) := by rfl
      simp; rw[lem]; simp; assumption)
  (by intro K' Δ' ih G Δ T K wf j
      replace j := Kinding.weaken K' j
      replace ih := ih G ([K'] ++ Δ) T[+1] K wf j
      simp at *
      have lem : ((+1 ∘ Ren.to (T := Ty) (fun x => x + Δ'.length))) = Ren.to (T := Ty) (fun x => x + Δ'.length + 1) := by
         clear ih j wf;
         have e := Ren.add_compose_distributes (T := Ty) (y := Δ'.length) (z := 1); rw[e]; simp;
         replace e := Ren.add_one_commutes (T := Ty) (y := Δ'.length); simp at e; rw[e]
      rw[lem] at ih; apply ih)
  G Δ T K wf j

theorem Kinding.closed_arbitrary_weakening : ∀ Δ',  ⊢ G ->  G&[] ⊢ T : K ->  G&Δ' ⊢ T : K := by
intro Δ' wf j
have lem1 := Kinding.closed j
have lem2 := Kinding.closed_lifting_lemma Δ' wf j
simp at *
replace lem1 := lem1 (Ren.to (λ x => x + Δ'.length))
rw[lem1] at lem2
apply lem2

end Core
