import Hs.HsTerm
import Hs.Monad
import SystemFD.Term
import SystemFD.Judgment

import Hs.Translator.Kinds

theorem compile_kind_shape_sound (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Term.IsKind k' := by
intro wf j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; constructor
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  constructor; assumption; assumption

theorem kind_shape_split_arrow_aux (k : Term) (acc : List Term):
  Term.IsKind k ->
  (∀ a ∈ acc, a.IsKind) ->
  Term.split_kind_arrow_aux acc k = .some (κs, ret_κ) ->
  ret_κ.IsKind ∧ ∀ k ∈ κs, k.IsKind := by
intro h1 h2 h3
induction acc, k using Term.split_kind_arrow_aux.induct generalizing κs ret_κ <;> simp at h3
case _ Γ f a ih =>
  cases h1; case _ h1a h2a =>
  have lem : ∀ (a : Term), a ∈ f :: Γ → a.IsKind := by
    intro x h
    simp at h; cases h
    case _ h => cases h; assumption
    case _ h => apply h2 x h
  have ih := @ih κs ret_κ h2a lem h3
  assumption
case _ =>
  cases h1
  cases h3.1; cases h3.2
  constructor; constructor
  assumption

theorem kind_shape_split_arrow {k : Term} :
  k.IsKind ->
  Term.split_kind_arrow k = some (κs, ret_κ) ->
  ret_κ.IsKind ∧ ∀ k ∈ κs, k.IsKind := by
 intros h1 h2; simp at h2
 have lem := @kind_shape_split_arrow_aux κs ret_κ k [] h1 (by intros; simp at *) h2
 assumption

theorem kinding_split_arrow_aux {Γ :  Ctx Term} (k : Term) (acc : List Term) :
  ⊢ Γ ->
  Γ ⊢ k : □ ->
  (∀ a ∈ acc, Γ ⊢ a : □) ->
  Term.split_kind_arrow_aux acc k = .some (κs, ret_κ) ->
  Γ ⊢ ret_κ : □ ∧ ∀ k ∈ κs, Γ ⊢ k : □ := by
intro wf j1 h1 h2
induction acc, k using Term.split_kind_arrow_aux.induct <;> simp at *
case _ ih =>
  cases j1; case _ j1a j1b =>
  have ih' := ih j1b j1a h1 h2
  assumption
case _ =>
  cases h2.1; cases h2.2
  constructor
  constructor; assumption
  intro k k_in_κs;
  have h1' := @h1 k k_in_κs
  assumption

theorem kinding_split_arrow {Γ : Ctx Term} {k : Term} :
  ⊢ Γ ->
  Γ ⊢ k : □ ->
  Term.split_kind_arrow k = .some (κs, ret_κ) ->
  Γ ⊢ ret_κ : □ ∧ ∀ k ∈ κs, Γ ⊢ k : □ := by
intro wf j h
apply kinding_split_arrow_aux k [] wf j
simp
assumption



theorem compile_kind_size (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  k.size = k'.size := by
intro wf  j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; simp
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  simp; rw[ih1, ih2]


theorem compile_kind_sound (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Γ ⊢ k' : c := by
intro wf e1 j;
induction c, k using compile_kind.induct generalizing k' <;> simp at *
case _ => cases j; constructor; assumption
case _ k1 k2 ih1 ih2 =>
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases e1;
  case _ e1 e2 =>
  replace ih1 := ih1 e1 h1;
  replace ih2 := ih2 e2 h2;
  constructor; assumption; assumption

theorem compile_star : compile_kind Γ □ `★ = DsM.ok ★ := by simp


theorem dsm_get_type_sound : ⊢ Γ ->
  DsM.toDsM s (Γ d@ h).get_type = .ok τ -> Γ ⊢ #h : τ := by
intro wf j
unfold DsM.toDsM at j
let gt := (Γ d@ h).get_type
generalize fh : Γ d@ h = f at *;
cases f;
all_goals try (
  simp at j;
  unfold Frame.get_type at j; simp at j
)
all_goals try (
  cases j; apply Judgment.var wf;
  unfold Frame.get_type; rw[fh]
)
