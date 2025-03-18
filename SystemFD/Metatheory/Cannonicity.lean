import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction

set_option maxHeartbeats 500000

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

theorem cannonical_ctor_var :
  Γ ⊢ #h : T ->
  Γ ⊢ T : ★ ->
  ValidCtorType Γ T ->
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

theorem cannonical_insttype_var :
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

theorem cannonical_ctor_head :
       Val Γ t ->
       Γ ⊢ t : τ ->
       Γ ⊢ τ : ★ ->
       t.neutral_form = .some (h, ts) ->
       (ValidCtorType Γ τ -> Γ.is_ctor h) ∨ (ValidInstType Γ τ -> Γ.is_insttype h) := by
intro vt tJ τJ tnf;
have tshape := Term.neutral_form_law (Eq.symm tnf)
rw[<-tshape] at tJ;
have hJ := inversion_apply_spine tJ;
cases hJ; case _ τ' hJ =>
cases hJ; case _ spTy hJ =>
cases vt;
any_goals(solve | cases tnf)
case app h_stable tnf' =>
  rw[tnf] at tnf'; cases tnf';
  cases hJ; case _ wf gt =>
  have τ'J := ctx_get_var_spine_type wf (Eq.symm gt) spTy τJ
  simp at h_stable;
  generalize fh : Γ d@ h = f at *;
  cases f;
  any_goals (solve | cases gt)
  all_goals (unfold Frame.is_stable_red at h_stable; simp at h_stable)
  all_goals (unfold Frame.get_type at gt; simp at gt; cases gt)
  case _ =>
    have h := ctx_get_var_type wf fh;
    have uniq := uniqueness_of_types h τ'J; cases uniq;
  case _ =>
    have h := ctx_get_datatype_kind wf fh;
    have uniq := uniqueness_of_types h τ'J; cases uniq;
  case _ =>
    apply Or.inl; intro vctor;
    simp; rw[fh]; unfold Frame.is_ctor; simp;
  case _ =>
    have h := ctx_get_opent_kind wf fh
    have uniq := uniqueness_of_types h τ'J; cases uniq;
  case _ =>
    apply Or.inr; intro vctor;
    simp; rw[fh]; unfold Frame.is_insttype; simp;


inductive ArrowLike  : (T : Term) -> Prop where
  | arrowt : ArrowLike (A -t> B)
  | allt : ArrowLike (∀[A] B)

inductive LambdaLike : (T : Term) -> Prop where
  | lam : LambdaLike (`λ[A] B)
  | lamt : LambdaLike (Λ[A] B)

@[simp]
abbrev CannonicalLambdaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, τ) =>
       Val Γ t ->
       Γ ⊢ t : τ ->
       Γ ⊢ τ : ★ ->
       ArrowLike τ ->
       (LambdaLike t ∨ ValidHeadVariable t Γ.is_ctor ∨ ValidHeadVariable t Γ.is_insttype)
| .wf => λ () => true

theorem cannonical_lambda :
  Judgment v Γ idx ->
  CannonicalLambdaType Γ v idx
  := by
intro j; induction j <;> simp at *
all_goals (intro h1 h2 h3 h4)
any_goals try (solve | cases h1; case _ h1 => cases h1)
any_goals try (solve | cases h3)
case _ Γ n T wf gt ih =>
  cases h1; case _ n_stable nnf =>
  simp at nnf; cases nnf; case _ e1 e2 =>
  subst e1; subst e2;
  generalize fh : Γ d@ n = f at *;
  unfold Frame.get_type at gt;
  cases h4;
  case _ =>
    split at gt;
    any_goals (solve | cases gt)
    any_goals (solve | unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable;
                       exfalso; rw[fh] at n_stable; simp at n_stable)
    all_goals (cases gt)
    case _ =>
      have lem := classification_lemma h3; simp at lem;
      cases lem;
      case _ =>
        have wfr := @frame_wf_by_index Γ n wf;
        have h := ctx_get_var_type wf fh;
        cases h
      case _ h =>
        cases h; case _ k h => cases h; case _ _ h => cases h; case _ h => cases h
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_datatype_kind wf fh;
      cases h;
    case _ =>
      apply Or.inr; apply Or.inl; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_ctor; simp
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_opent_kind wf fh;
      cases h;
    case _ =>
      apply Or.inr; apply Or.inr; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_insttype; simp
  case _ =>
    split at gt;
    any_goals (solve | cases gt)
    any_goals (solve | unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable;
                       exfalso; rw[fh] at n_stable; simp at n_stable)
    all_goals (cases gt)
    case _ =>
      have lem := classification_lemma h3; simp at lem;
      cases lem;
      case _ =>
        have wfr := @frame_wf_by_index Γ n wf;
        have h := ctx_get_var_type wf fh;
        cases h
      case _ h =>
        cases h; case _ k h => cases h; case _ _ h => cases h; case _ h => cases h
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_datatype_kind wf fh;
      cases h;
    case _ =>
      apply Or.inr; apply Or.inl; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_ctor; simp
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_opent_kind wf fh;
      cases h;
    case _ =>
      apply Or.inr; apply Or.inr; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_insttype; simp

case _ Γ f _ _ _ fJ _ _ ih => -- appk bogus case
  cases h1; case _ n ts n_stable ts' =>
  simp at ts'; rw [Option.bind_eq_some] at ts';  cases ts'; case _ w fnf =>
  cases fnf; case _ fnf ts' =>
  cases ts';
  have vf : Val Γ f := by constructor; assumption; assumption
  generalize fh : Γ d@ w.fst = f at *;
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h; case _ k1 k2 =>
    have h := uniqueness_of_types h3 k2; cases h;
  case _ h =>
    cases h; case _ w h =>
    cases h; case _ wk arrk =>
    cases arrk; cases wk;

case lam Γ A t B ih1 ih2 =>  constructor; constructor

case app Γ f A B a B' fJ aJ h0 ih1 ih2 =>
  cases h1; case _ n ts n_stable h1 =>
  simp at h1; rw[Option.bind_eq_some] at h1;
  cases h1;  case _ ts' fnf =>
  cases fnf; case _ fnf ts' =>
  cases ts'; have h := Val.app fnf n_stable;
  simp at *;
  have lem := classification_lemma fJ; simp at lem;
  cases lem;
  case _ h => cases h
  case _ h =>
    cases h; case _ k h =>
    cases h; case _ k h =>
    cases h; case _ aK bK =>
    have arrK := Judgment.arrow aK bK;
    have ih := ih1 h fJ arrK (ArrowLike.arrowt); cases ih;
    case _ h =>
      cases h;
      case _ => cases fnf
      case _ => cases fnf
    case _ h =>
      cases h;
      case _ h =>
        apply Or.inr; apply Or.inl;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_app f a ts'.1 ts'.2 fnf; symm at fanf;
        apply Exists.intro (ts'.1, ts'.snd ++ [(.term, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; simp; assumption;
      case _ h =>
        apply Or.inr; apply Or.inr;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_app f a ts'.1 ts'.2 fnf; symm at fanf;
        apply Exists.intro (ts'.1, ts'.snd ++ [(.term, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; simp; assumption;
case _ ih1 _ =>
  cases h1;
  case _ h => cases h
  case _ => constructor; constructor

case _ Γ f A B a B' fJ aJ _ ih1 ih2 =>
  cases h1; case _ n ts n_stable h1 =>
  simp at h1; rw[Option.bind_eq_some] at h1;
  cases h1;  case _ ts' fnf =>
  cases fnf; case _ fnf ts' =>
  cases ts'; have h := Val.app fnf n_stable;
  simp at *;
  have lem := classification_lemma fJ; simp at lem;
  cases lem;
  case _ h => cases h
  case _ h =>
    cases h; case _ k h =>
    cases h; case _ k h =>
    cases h; case _ aK bK =>
    have arrK := Judgment.allt aK bK;
    have ih := ih1 h fJ arrK (ArrowLike.allt); cases ih;
    case _ h =>
      cases h;
      case _ => cases fnf
      case _ => cases fnf
    case _ h =>
      cases h;
      case _ h =>
        apply Or.inr; apply Or.inl;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_appt f a ts'.1 ts'.2 fnf; symm at fanf;
        apply Exists.intro (ts'.1, ts'.snd ++ [(.type, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; simp; assumption;
      case _ h =>
        apply Or.inr; apply Or.inr;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_appt f a ts'.1 ts'.2 fnf; symm at fanf;
        apply Exists.intro (ts'.1, ts'.snd ++ [(.type, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; simp; assumption;
case _ ih2 => cases h4
