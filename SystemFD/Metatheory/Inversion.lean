import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Uniqueness

theorem inversion_apply_spine :
  Γ ⊢ t.apply_spine sp : A ->
  ∃ B, Γ ⊢ t : B
:= by
intro j; induction sp generalizing Γ t A <;> simp at *
case _ => exists A
case _ hd tl ih =>
  cases hd; case _ v a =>
  cases v <;> simp at *
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 j3 =>
    apply Exists.intro _; apply j1
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 j3 =>
    apply Exists.intro _; apply j1
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j =>
    apply Exists.intro _; apply j

theorem apply_spine_uniform :
  Γ ⊢ a : A ->
  Γ ⊢ b : A ->
  Γ ⊢ a.apply_spine sp : B ->
  Γ ⊢ b.apply_spine sp : B
:= by
intro j1 j2 j3
induction sp generalizing Γ a b A B <;> simp at *
case _ =>
  have lem := uniqueness_of_types j1 j3; subst lem
  apply j2
case _ hd tl ih =>
  cases hd; case _ v t =>
  cases v <;> simp at *
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ U V q1 q2 q3 =>
      have lem1 := uniqueness_of_types j1 q1; subst lem1
      have lem2 : Γ ⊢ (a `@ t) : (V β[t]) := by
        constructor; apply q1; apply q2; simp
      have lem3 : Γ ⊢ (b `@ t) : (V β[t]) := by
        constructor; apply j2; apply q2; simp
      apply ih lem2 lem3 j3
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ U V q1 q2 q3 =>
      have lem1 := uniqueness_of_types j1 q1; subst lem1
      have lem2 : Γ ⊢ (a `@t t) : (V β[t]) := by
        constructor; apply q1; apply q2; simp
      have lem3 : Γ ⊢ (b `@t t) : (V β[t]) := by
        constructor; apply j2; apply q2; simp
      apply ih lem2 lem3 j3
  case _ =>
    have lem := inversion_apply_spine j3
    cases lem; case _ D lem =>
    cases lem; case _ U q1 q2 =>
      have lem1 := uniqueness_of_types j1 q2; subst lem1
      have lem2 : Γ ⊢ (a `@k t) : D := by
        constructor; apply q2; apply q1
      have lem3 : Γ ⊢ (b `@k t) : D := by
        constructor; apply j2; apply q1
      apply ih lem2 lem3 j3

@[simp]
abbrev GetCtxLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ _ => True
| .wf => λ () => ∀ x,
  (∀ {T t}, Γ d@ x = .term T t -> Γ ⊢ #x : T ∧ Γ ⊢ t : T)

theorem ctx_get_lemma : Judgment v Γ ix -> GetCtxLemmaType Γ v ix := by
have lem1 : ∀ {Γ x T t}, (Γ d@ x).apply S = Frame.term T t ->
  ∃ (T' t' : Term), (Γ d@ x) = Frame.term T' t'
:= by
  sorry
intro j; induction j <;> simp at *
case _ Γ h ih =>
  intro x; cases x <;> simp at *
  case _ =>
    intro T t h1
    unfold Frame.apply at h1; simp at h1
  case _ x =>
    intro T t h1
    have h2 := lem1 h1
    cases h2; case _ T' h2 =>
    cases h2; case _ t' h2 =>
      rw [h2] at h1; unfold Frame.apply at h1; simp at h1
      cases h1; case _ h1 h2 =>
        subst h1; subst h2
        replace ih := ih x h2
        apply And.intro
        apply weaken_empty ih.1
        apply weaken_empty ih.2
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry

theorem ctx_get_term_well_typed :
  ⊢ Γ ->
  Γ d@ x = .term T t ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by
intro h1 h2
have lem := ctx_get_lemma h1; simp at lem
apply (lem x) h2

theorem ctx_get_instance_well_typed :
  ⊢ Γ ->
  Γ d@ x = .openm T ->
  ixs = instance_indices' Γ 0 x [] ->
  t ∈ get_instances Γ ixs ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by sorry

theorem ctx_get_opent_kind : ⊢ Γ -> Γ d@ x = .opent t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry

theorem ctx_get_datatype_kind : ⊢ Γ -> Γ d@ x = .datatype t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry

theorem ctx_get_var_type : ⊢ Γ -> Γ d@ x = .kind t -> Γ ⊢ t : .kind := by
intros wΓ h;
sorry


theorem ctx_get_var_no_eq_type :
  ⊢ Γ ->
  Γ.is_stable_red x ->
  ¬ (Γ d@ x).get_type = .some (A ~ B)
:= by
intros wΓ nsx;
simp_all;
unfold Frame.is_stable_red at nsx;
split at nsx;
any_goals(solve | unfold Frame.get_type; simp_all)
case _ =>
  simp_all; unfold Frame.get_type; intro h; split at h;
  any_goals (cases h)
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry
  case _ h => sorry





theorem invert_eq_kind : Γ ⊢ (A ~ B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_arr_kind : Γ ⊢ (A -t> B) : w -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem invert_all_kind : (Γ ⊢ ∀[ A ] B : w) -> w = ★ := by
intros eqJ; cases eqJ; simp_all;

theorem lamt_typing_unique : Γ ⊢ Λ[A]b : t -> ∃ B', t = ∀[A] B' := by
intros tJ; cases tJ;
case _ => simp_all;

theorem lam_typing_unique : Γ ⊢ `λ[A]b : t -> ∃ B', (t = (A -t> B')) := by
intros tJ; cases tJ;
case _ => simp_all;

theorem refl_typing_unique : Γ ⊢ refl! A : t -> (t = (A ~ A)) := by
intros tJ; cases tJ;
case _ => simp_all;
