import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.FrameWf

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

theorem ctx_get_term_well_typed :
  ⊢ Γ ->
  Γ d@ x = .term T t ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by
intro h1 h2
have lem1 := frame_wf_by_index x h1
have lem2 := frame_wf_implies_typed_var T lem1 (by rw [h2]; unfold Frame.get_type; simp)
rw [h2] at lem1; cases lem1
case _ j1 j2 => apply And.intro lem2 j2

theorem ctx_get_instance_well_typed :
  ⊢ Γ ->
  Γ d@ x = .openm T ->
  ixs = instance_indices Γ 0 x [] ->
  t ∈ get_instances Γ ixs ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by
intro h1 h2 h3 h4
have lem1 := frame_wf_by_index x h1
have lem2 := frame_wf_implies_typed_var T lem1 (by rw [h2]; unfold Frame.get_type; simp)
have lem3 := get_instances_sound h3 h4
cases lem3; case _ i lem3 =>
  have lem4 := frame_wf_by_index i h1
  rw [lem3] at lem4; cases lem4
  case _ A q1 q2 =>
    rw [<-q1] at h2; injection h2 with e
    subst e
    apply And.intro lem2 q2

theorem ctx_get_opent_kind : ⊢ Γ -> Γ d@ x = .opent t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_datatype_kind : ⊢ Γ -> Γ d@ x = .datatype t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_var_type : ⊢ Γ -> Γ d@ x = .kind t -> Γ ⊢ t : .kind := by
intro h1 h2
have lem1 := frame_wf_by_index x h1
rw [h2] at lem1; cases lem1
case _ j => apply j

theorem ctx_get_var_no_eq_type :
  ⊢ Γ ->
  Γ.is_stable_red x ->
  ¬ (Γ d@ x).get_type = .some (A ~ B)
:= by
intro h1 h2 h3
have lem1 := frame_wf_by_index x h1
simp at *; generalize fdef : Γ d@ x = f at *
cases lem1
all_goals (
  unfold Frame.get_type at h3
  unfold Frame.is_stable_red at h2; simp at *)
case _ j => subst h3; cases j
case _ j => subst h3; cases j
case _ j1 j2 =>
  subst h3; cases j2
  case _ j2 =>
    unfold ValidHeadVariable at j2; simp at j2
case _ j => subst h3; cases j
case _ j1 j2 =>
  subst h3; cases j2
  case _ j2 =>
    unfold ValidHeadVariable at j2; simp at j2

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
