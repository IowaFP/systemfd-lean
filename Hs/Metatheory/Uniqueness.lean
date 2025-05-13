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


-- @[simp]
-- abbrev WellSortedKindInversion : (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Prop
-- | .kind => λ Γ => λ (t, τ) => Γ ⊢κ t : τ -> τ = `□
-- | _ => λ _ => λ _ => true

-- theorem well_sorted_kind_inversion_lemma :
--   HsJudgment v Γ idx -> WellSortedKindInversion v Γ idx := by
-- intro j;
-- induction j <;> simp at *;

-- theorem well_sorted_kind_inversion :
--   Γ ⊢κ t : τ -> τ = `□ := by
-- intro j;
-- have lem := well_sorted_kind_inversion_lemma j;
-- apply lem j;
------------------------------------
-- Judgments For Types
------------------------------------

theorem types_have_unique_kinds :
  Γ ⊢τ t : k ->
  Γ ⊢τ t : k' ->
  k = k' := by
intro j1 j2;
induction t generalizing k k'
all_goals (cases j1)
case _ =>
  cases j2
  case _ h2 _ _ _ h1 =>
  rw [<-h1] at h2; injection h2;
all_goals(cases j2)
case _ f a ih1 ih2 k'' hk1 ht1 hk2 ht2 B hk3 ht3 hk4 ht4 =>
  have u := @ih2 k'' B ht1 ht3; subst u;
  have u := @ih1 (k'' `-k> k) (k'' `-k> k') ht2 ht4;
  simp at u; apply u;
case _ => rfl
case _ => rfl
case _ => rfl


theorem kinds_subst_eff_free σ : (k : HsTerm) ->
  (Γ ⊢κ k : s) ->
  [σ] k = k := by
intro k j;
cases j;
case _ => simp
case _ A B j1 j2 =>
  have h1 := kinds_subst_eff_free σ A j1
  have h2 := kinds_subst_eff_free σ B j2
  simp; constructor; assumption; assumption
termination_by h => h.size


theorem kinds_subst_eff_free2 : (k : HsTerm) ->
  (Γ ⊢κ k : s) ->
  ∀ σ, [σ] k = k := by
intro k j σ;
cases j;
case _ => simp
case _ A B j1 j2 =>
  have h1 := kinds_subst_eff_free σ A j1
  have h2 := kinds_subst_eff_free σ B j2
  simp; constructor; assumption; assumption


theorem idempotent_substitution_kinding σ : (k : HsTerm) ->
  (Γ ⊢κ k : s) ->
  (Γ ⊢κ ([σ]k) : ([σ]s)) = (Γ ⊢κ k : s) := by
intro k j
cases j;
case _ => simp
case _ A B j1 j2 =>
  simp;
  have h1 := idempotent_substitution_kinding σ A j1;
  have h2 := idempotent_substitution_kinding σ B j2;
  have h3 := kinds_subst_eff_free σ A j1;
  have h4 := kinds_subst_eff_free σ B j2;
  congr
termination_by h => h.size

theorem kinds_subst_eff_free_types σ : (k : HsTerm) ->
  (Γ ⊢τ t : k) ->
  (Γ ⊢τ t : ([σ]k)) = (Γ ⊢τ t : k) := by
intro k j1
cases j1;
all_goals (simp)
case _ f A a ja jak jf jk =>
  have u2 := kinds_subst_eff_free σ k jk; rw[u2]
case _ x wf _ gt jk =>
  have u2 := kinds_subst_eff_free σ k jk; rw[u2]


theorem idempotent_substitution_typing σ : (k : HsTerm) ->
  (Γ ⊢τ t : k) ->
  (Γ ⊢τ ([σ]t) : ([σ]k)) = (Γ ⊢τ ([σ]t) : k) := by
intro k j
cases j;
all_goals (simp)
case _ f A jk =>
  have u := kinds_subst_eff_free σ k jk; rw [u]
case _ jk =>
  have u := kinds_subst_eff_free σ k jk; rw [u]

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
case _ Γ _ _ _ _ jf ja jka jkb ih1 ih2 _ _ =>
  intro j1 j2;
  cases j1; cases j2;
  simp at *;
  case _ _ jka1 ja1 jkb1 jf1 _ jka2 ja2 jkb2 jf2 =>
  have lem := types_have_unique_kinds ja1 ja2; cases lem; simp at *;
  have lem := types_have_unique_kinds ja ja1; cases lem;
  have lem := ih1 jf1 jf2; cases lem
  have lem := ih2 ja1 ja2; cases lem; simp;
  have lem := kinds_have_unique_judgments h jkb1 jkb2; cases lem;
  have lem := kinds_have_unique_judgments h jka1 jka2; cases lem;
  simp
case _ Γ _ _ _ _ _ _ _ _ =>
  intro j1 j2;
  cases j1; cases j2;
  case _ wf1 _ h1 _ wf2 _ h2 _ =>
  have lem :=  kinds_have_unique_judgments h h1 h2; cases lem;
  simp at *;
  apply @h Γ wf1 wf2;

theorem types_have_unique_judgments :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢τ t : k) ->
  (j2 : Γ ⊢τ t : k) ->
  j1 = j2 := by
intro h j1 j2;
apply types_have_unique_judgments_lemma h j2 j1 j2;


theorem arrow_kind_inversion :
  Γ ⊢τ (A → B) : k -> k = `★ := by
intro j; cases j; rfl

theorem farrow_kind_inversion :
  Γ ⊢τ (A ⇒ B) : k -> k = `★ := by
intro j; cases j; rfl

theorem all_kind_inversion :
  Γ ⊢τ (`∀{A} B) : k -> k = `★ := by
intro j; cases j; rfl
