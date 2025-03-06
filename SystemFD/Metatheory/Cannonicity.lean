import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction

inductive Val : Ctx Term -> Term -> Prop where
| app : t.neutral_form = .some (n, ts)
      -> (Γ.is_stable_red n)
      -> Val Γ t
| lam :  Val Γ (`λ[a] b)
| lamt : Val Γ (Λ[A] b)
| refl : Val Γ (refl! _)
| star : Val Γ ★
| arr :  Val Γ (A -t> B)
| arrk : Val Γ (A -k> B)
| all : Val Γ (∀[A]B)
| eq : Val Γ (A ~ B)

theorem refl_var_spine_lemma :
  Γ.is_stable_red n ->
  Γ ⊢ (#n).apply_spine sp : (A ~ B) ->
  False
:= by
intro j1 j2
have lem := inversion_apply_spine j2
cases lem; case _ C lem =>
cases lem; case _ h1 h2 =>
cases h2; case _ j3 j4 =>
  have lem := classification_lemma j2 <;> simp at lem
  cases lem
  case _ lem => cases lem
  case _ lem =>
    cases lem; case _ K lem =>
    cases lem.2; case _ q1 q2 q3 =>
      apply ctx_get_var_no_spine_eq_type j3 j1
      rw [j4]; apply lem.2; apply h1

theorem refl_is_val :
  Γ ⊢ η : (A ~ B) ->
  Val Γ η ->
  η = refl! A ∧ A = B
:= by
intros ηJ vη; induction vη;
any_goals(solve | cases ηJ)
case _ Γ t n ts tnf n_stable =>
     symm at tnf; replace tnf := Term.neutral_form_law tnf;
     subst tnf;
     exfalso;
     apply (refl_var_spine_lemma n_stable ηJ);
case _ => cases ηJ; case _ fJ =>
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h; case _ h => cases h
  case _ h => apply And.intro rfl rfl

theorem cannonical_ctor_head :
  Γ ⊢ #h : T ->
  Γ ⊢ T : ★ ->
  ValidCtor Γ T ->
  Γ.is_stable_red h ->
  Γ.is_ctor h := by
intros tJ tstar vctor n_stable;
cases tJ; case _ wf h1 =>
  have h2 := @frame_wf_by_index Γ h wf;
  have h3 := @frame_wf_implies_typed_var Γ h T h2 h1;
  generalize fh : Γ d@ h = f at *;
  unfold Frame.get_type at h1;
  split at h1;
  any_goals (solve | simp at *)
  all_goals (unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable)
  any_goals (solve |  rw [fh] at n_stable; simp at n_stable)
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_var_type wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_datatype_kind wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ => unfold Ctx.is_ctor; unfold Frame.is_ctor; rw [fh]
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_opent_kind wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ =>
    injection h1 with h1; cases h1;
    cases h2; case _ vit =>
    exfalso
    apply datatype_opent_distinct vctor vit



theorem cannonical_insttype_head :
  Γ ⊢ #h : T ->
  Γ ⊢ T : ★ ->
  ValidInstType Γ T ->
  Γ.is_stable_red h ->
  Γ.is_insttype h := by
intros tJ tstar vctor n_stable;
cases tJ; case _ wf h1 =>
  have h2 := @frame_wf_by_index Γ h wf;
  have h3 := @frame_wf_implies_typed_var Γ h T h2 h1;
  generalize fh : Γ d@ h = f at *;
  unfold Frame.get_type at h1;
  split at h1;
  any_goals (solve | simp at *)
  all_goals (unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable)
  any_goals (solve |  rw [fh] at n_stable; simp at n_stable)
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_var_type wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_datatype_kind wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ =>
    injection h1 with h1; cases h1;
    cases h2; case _ vit =>
      exfalso
      apply datatype_opent_distinct vit vctor
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_opent_kind wf fh;
    have uniq := uniqueness_of_types tstar lem;
    cases uniq;
  case _ =>
    injection h1 with h1; cases h1;
    simp; rw [fh]; unfold Frame.is_insttype; simp;
