import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

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
:= by sorry

theorem ctx_get_term_well_typed :
  ⊢ Γ ->
  Γ d@ x = .term T t ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by sorry

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
