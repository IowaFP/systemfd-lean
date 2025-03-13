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

theorem cannonical_ctor_var :
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


-- @[simp]
-- abbrev ValidCtorSubtInvType : (v : JudgmentVariant) -> Ctx Term -> JudgmentArgs v -> Prop
-- | .prf => λ Δ => λ (A, τ) => ∀ Γ σ,
--     (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
--     (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
--     ValidCtor Δ ([σ]A) ->
--     Δ ⊢ A : τ ->
--     (★ = τ) ->
--     ValidCtor Γ A

-- | .wf  => λ _ => λ () => true

-- theorem valid_ctor_subst_inv :
--   Judgment v Γ idx ->
--   ValidCtorSubtInvType v Γ idx
-- := by
-- intro j; induction j <;> simp at *;
-- all_goals (intro Γ σ f1 f2 vctor tJ)
-- all_goals try (intro e; subst e)
-- any_goals try (solve | cases tJ; case _ h _ => cases h)
-- any_goals try (solve | cases tJ; case _ h => cases h)
-- case _ =>
--   sorry
-- case _ =>
--   sorry
-- case _ aJ bJ ih1 ih2 =>
--   have ih1' := ih1 Γ σ f1 f2; -- stuck here as we have no easy way to build ValidCtor Γ ([σ] A)
--   have ih2' := ih2 Γ σ
--   sorry
-- case _ => cases vctor; sorry -- bogus case
-- case _ => exfalso; apply valid_ctor_not_equality vctor
-- case _ =>
--   sorry
-- case _ =>
--   sorry
-- case _ =>
--   sorry

theorem valid_head_variable_subst_inv test σtest :
  (∀ n, test n -> ∃ y, σ n = .re y ∧ σtest y) ->
  (z = [σ]A) ->
  ValidHeadVariable z σtest ->
  ValidHeadVariable A test
:= by
intros f1 eq j; induction j <;> simp at *;
case _ w fnf =>
  unfold ValidHeadVariable;
  exists w;
  sorry


theorem valid_ctor_subst_inv :
    (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
    (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
    Γ ⊢ A : τ ->
    (★ = τ) ->
    ([σ] A = Z) ->
    ValidCtor Δ Z ->
    ValidCtor Γ A
:= by
intro f1 f2 tJ eq1 eq2 j; induction j <;> simp at *;
case refl vhv =>
  subst eq1;
  cases vhv; case _ Rnf =>
  cases Rnf; case _ Rnf test =>

  sorry
case arrow ih =>

  sorry
case all ih =>

  sorry

inductive ArrowLike  : (T : Term) -> Prop where
  | arrowt : ArrowLike (A -t> B)
  | allt : ArrowLike (∀[A] B)

@[simp]
abbrev CannonicalCtorHeadType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, τ) => ∀ h ts,
       Val Γ t ->
       Γ ⊢ t : τ ->
       Γ ⊢ τ : ★ ->
       t.neutral_form = .some (h, ts) ->
       ValidCtor Γ τ ->
       Γ.is_ctor h
| .wf => λ () => true

theorem cannonical_ctor_head :
  Judgment v Γ idx ->
  CannonicalCtorHeadType Γ v idx
 := by
intros j; induction j <;> simp at *
all_goals (intro n sp tv tJ τJ)
any_goals try (solve | cases tv; case _ h => cases h)
any_goals try (solve | apply Exists.intro 0;
                         intro h; cases h; case _ h => cases h)
case _ n τ wf gt _ =>
  intro e1 e2 vctor;
  subst e1; subst e2;
  cases tv; case _ n sp nst ntf =>
  cases ntf;
  apply cannonical_ctor_var;
  assumption; assumption; assumption; assumption

all_goals (intro fnf vctor)
case appk fJ aJ ih _ => -- bogus case
  have lem := classification_lemma fJ; simp at lem
  cases lem;
  case _ h =>
    cases h; case _ h =>
    have uniq := uniqueness_of_types h τJ; cases uniq
  case _ h =>
    cases h; case _ h =>
    cases h; case _ h h1 =>
    cases h1; case _ h => cases h

case _ Γ f A B a B' fJ aJ eq' ih1 _ =>
  cases tv; case _ n ts ns fanf =>
  simp at fanf; rw[Option.bind_eq_some] at fanf;
  cases fanf; case _ w fnf' =>
  cases fnf'; case _ fnf' fanf' =>
  rw[Option.bind_eq_some] at fnf;
  cases fnf; case _ w fnf =>
  cases fnf; case _ fnf tsh =>
  cases tsh;
  rw[fnf] at fnf'; cases fnf';
  cases fanf';
  have lem := classification_lemma fJ; simp at lem;
  cases lem;
  case _ h => cases h;
  case _ h =>
  cases h; case _ h =>
  cases h; case _ arrJ =>
  have arrK := invert_arr_kind arrJ; subst arrK;
  have h1 : ValidCtor (.empty::Γ) B := by
    apply valid_ctor_subst_inv _ _ _ _ (Eq.symm eq') vctor; apply ★;
    case _ =>
      intro n y σ; induction n <;> simp at *;
      rw[σ]; rw[Frame.apply_compose]; simp -- f1
    case _ =>
      intro n st; induction n <;> simp at *;
      unfold Frame.is_stable at st; unfold Frame.apply at st; simp at *;
    case _ => rw[eq'] at τJ; cases arrJ; assumption -- well typed
    case _ => rfl -- ★ = ★
  have h2 :ValidCtor Γ (A -t> B)  := ValidCtor.arrow h1;
  apply ih1 w.fst w.snd (Val.app fnf ns) fJ arrJ fnf h2;

case appt Γ f A B a B' fJ aJ eq' ih1 _ =>
  cases tv; case _ n ts ns fanf =>
  simp at fanf; rw[Option.bind_eq_some] at fanf;
  cases fanf; case _ w fnf' =>
  cases fnf'; case _ fnf' fanf' =>
  rw[Option.bind_eq_some] at fnf;
  cases fnf; case _ w fnf =>
  cases fnf; case _ fnf tsh =>
  cases tsh;
  rw[fnf] at fnf'; cases fnf';
  cases fanf';
  have lem := classification_lemma fJ; simp at lem;
  cases lem;
  case _ h => cases h;
  case _ h =>
  cases h; case _ h =>
  cases h; case _ arrJ =>
  have arrK := invert_all_kind arrJ; subst arrK;
  have h1 : ValidCtor (.kind A::Γ) B := by
    apply valid_ctor_subst_inv _ _ _ _ (Eq.symm eq') vctor; apply ★;
    case _ =>
      intro n y σ; induction n <;> simp at *;
      rw[σ]; rw[Frame.apply_compose]; simp -- f1
    case _ =>
      intro n st; induction n <;> simp at *;
      unfold Frame.is_stable at st; unfold Frame.apply at st; simp at *;
    case _ => rw[eq'] at τJ; cases arrJ; assumption -- well typed
    case _ => rfl -- ★ = ★
  have h2 :ValidCtor Γ (∀[A] B)  := ValidCtor.all h1;
  apply ih1 w.fst w.snd (Val.app fnf ns) fJ arrJ fnf h2;

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
       ((LambdaLike t) ∨ (ValidHeadVariable t Γ.is_ctor ∨ ValidHeadVariable t Γ.is_insttype))
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
