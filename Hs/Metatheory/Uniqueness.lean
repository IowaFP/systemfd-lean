import Hs.Algorithm
import Hs.HsJudgment

------------------------------------
-- Sorting Judgments
------------------------------------

theorem kinding_uniqueness :
  Γ ⊢κ τ : k ->
  Γ ⊢κ τ : k' ->
  k = k' :=
 by
intro j1 j2
induction τ generalizing Γ k k'
case _ => cases j1; cases j2; rfl
all_goals (cases j1)
case _ ih1 ih2 kl1 kl2 =>
  cases j2; rfl;

@[simp]
abbrev SortJudgmentUniquenessType : (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Prop
| .kind => λ Γ => λ (t, τ) =>
   (j1 : Γ ⊢κ t : τ) -> (j2 : Γ ⊢κ t : τ) -> j1 = j2
| _ => λ _ => λ _ => true

theorem kinds_have_unique_judgments_lemma :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  HsJudgment v Γ idx -> SortJudgmentUniquenessType v Γ idx
  := by
intro h j;
induction j <;> simp at *;
case _ Γ _ _ =>
  intro j1 j2;
  cases j1; case _ j1 =>
  cases j2; case _ j2 =>
  have h' := @h Γ j1 j2;
  cases h'; simp
case _ Γ _ _ _ _ ih1 ih2 =>
  intro j1 j2;
  cases j1; cases j2;
  case _ ja1 jb1 ja2 jb2 =>
  have h1 := @ih1 ja1 ja2;
  have h2 := @ih2 jb1 jb2;
  cases h1; cases h2; simp;

theorem kinds_have_unique_judgments :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢κ t : τ) ->
  (j2 : Γ ⊢κ t : τ) ->
  j1 = j2 := by
intro h j1 j2;
apply kinds_have_unique_judgments_lemma h j2 j1 j2;

theorem kinds_compiling_uniqueness :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢κ t : τ) ->
  (j2 : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j1 = .some t1 ->
  compile_kind Γ t τ j2 = .some t2 ->
  t1 = t2 := by
intro h j1 j2 c1 c2
have lem := kinds_have_unique_judgments h j1 j2; cases lem;
rw[c1] at c2; injection c2

------------------------------------
-- Judgments For Types
------------------------------------

theorem types_have_unique_kinds :
  Γ ⊢τ t : k ->
  Γ ⊢τ t : k' ->
  k = k' := by
intro j1 j2;
induction t generalizing Γ k k';
all_goals (cases j1)
case _ =>
  cases j2
  case _ h2 _ _ h1 =>
  rw [<-h1] at h2; injection h2;
all_goals(cases j2)
case _ ih1 ih2 A j1 j2 A' j1' j2' =>
  have u := @ih2 Γ A A' j1 j1'; subst u;
  have u := @ih1 Γ (A `-k> k) (A `-k> k') j2 j2';
  simp at u; apply u;
case _ => rfl
case _ => rfl
case _ => rfl

@[simp]
abbrev KindingJudgmentsUniquessType : (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Prop
| .type => λ Γ => λ (t, τ) =>
   (j1 : Γ ⊢τ t : τ) -> (j2 : Γ ⊢τ t : τ) -> j1 = j2
| _ => λ _ => λ _ => true

theorem types_have_unique_judgments_lemma :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  HsJudgment v Γ idx -> KindingJudgmentsUniquessType v Γ idx := by
intro h j;
induction j <;> simp at *;
case _ Γ _ _ ja jb ih1 ih2 =>
  intro j1 j2;
  cases j1; cases j2; simp at *;
  case _ ja1 jb1 ja2 jb2 =>
  have lem := kinds_have_unique_judgments h ja1 ja2; cases lem;
  have lem := ih1 jb1 jb2; cases lem; simp
case _ Γ _ _ ja jb ih1 ih2 =>
  intro j1 j2;
  cases j1; cases j2; simp at *;
  case _ ja1 jb1 ja2 jb2 =>
  have lem := types_have_unique_kinds ja1 ja2; cases lem;
  have lem := types_have_unique_kinds ja ja1; cases lem;
  have lem := ih1 ja1 ja2; cases lem
  have lem := ih2 jb1 jb2; cases lem; simp
case _ Γ _ _ ja _ jb ih1 ih2 =>
  intro j1 j2;
  cases j1; cases j2; simp at *;
  case _ ja1 _ jb1 ja2 _ jb2 =>
  have lem := types_have_unique_kinds ja1 ja2; cases lem;
  have lem := types_have_unique_kinds ja ja1; cases lem;
  have lem := ih1 ja1 ja2; cases lem
  have lem := ih2 jb1 jb2; cases lem; simp
case _ Γ _ _ _ _ jf ja ih1 ih2  =>
  intro j1 j2;
  cases j1; cases j2;
  simp at *;
  case _ ja1 jf1 _ ja2 jf2 =>
  have lem := types_have_unique_kinds ja1 ja2; cases lem; simp at *;
  have lem := types_have_unique_kinds ja ja1; cases lem;
  have lem := ih1 jf1 jf2; cases lem
  have lem := ih2 ja1 ja2; cases lem; simp
case _ Γ _ _ _ _ _ _ =>
  intro j1 j2;
  cases j1; cases j2;
  simp at *;
  case _ wf1 _ _ wf2 _ _ => apply @h Γ wf1 wf2;

theorem types_have_unique_judgments :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢τ t : k) ->
  (j2 : Γ ⊢τ t : k) ->
  j1 = j2 := by
intro h j1 j2;
apply types_have_unique_judgments_lemma h j2 j1 j2;

theorem compile_type_uniqueness :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢τ τ : k) ->
  (j2 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some t1 ->
  compile_type Γ τ k j2 = .some t2 ->
  t1 = t2
  := by
intro h j1 j2 c1 c2;
have lem := types_have_unique_judgments h j1 j2; cases lem;
rw[c1] at c2; injection c2;
