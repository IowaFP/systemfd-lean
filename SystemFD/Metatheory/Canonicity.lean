import SystemFD.Term
import SystemFD.Ctx
import SystemFD.Judgment
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.FrameWf
import SystemFD.Metatheory.Inversion
import SystemFD.Reduction

set_option maxHeartbeats 500000


inductive Val : Ctx Term -> Term -> Prop where
| app x sp :
  t.neutral_form = .some (x, sp) ->
  Γ.is_stable_red x ∨ OpenVarVal Γ x sp ->
  Val Γ t
| choice : Val Γ t1 -> Val Γ t2 -> Val Γ (t1 ⊕ t2)
| lam :  Val Γ (`λ[a] b)
| lamt : Val Γ (Λ[A] b)
| refl : Val Γ (refl! K A)
| star : Val Γ ★
| arr :  Val Γ (A -t> B)
| arrk : Val Γ (A -k> B)
| all : Val Γ (∀[A]B)
| eq : Val Γ (A ~[K]~ B)

theorem refl_var_spine_lemma :
  Γ.is_stable_red n ∨ OpenVarVal Γ n sp ->
  Γ ⊢ (#n).apply_spine sp : (A ~[K]~ B) ->
  False
:= by
intro j1 j2
have lem := inversion_apply_spine j2
cases lem; case _ C lem =>
cases lem; case _ h1 h2 =>
cases h2; case _ j3 j4 =>
cases j3; case _ j3 j5 =>
have lem := classification_lemma j2 <;> simp at lem
cases lem
case _ lem => cases lem
case _ lem =>
  cases lem; case _ K lem =>
  cases lem.2; case _ q1 q2 q3 =>
    apply ctx_get_var_no_spine_eq_type j3 j1
    rw [j5]; apply lem.2; apply h1

theorem refl_is_val :
  Γ ⊢ η : (A ~[K]~ B) ->
  Val Γ η ->
  (η = refl! K A ∧ A = B)
    ∨ (∃ (c1 c2 : Term), η = (c1 ⊕ c2))
:= by
intros ηJ vη; induction vη;
any_goals (solve | cases ηJ)
case refl =>
  cases ηJ; case _ j1 j2 =>
  have lem := classification_lemma j2; simp at lem; cases lem;
  case _ h => subst h; cases j1
  case _ h => apply Or.inl; apply And.intro rfl rfl
case app x sp j1 j2 =>
  replace tnf := Term.neutral_form_law (Eq.symm j1);
  subst tnf;
  exfalso;
  apply (refl_var_spine_lemma j2 ηJ);
case choice =>
  apply Or.inr; apply Exists.intro _
  apply Exists.intro _; rfl

theorem cannonical_var :
  Γ ⊢ #h : T ->
  Γ ⊢ T : ★ ->
  Γ.is_stable_red h ->
  (Γ.is_ctor h ∨ Γ.is_insttype h) := by
intros tJ tstar n_stable;
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
    have lem1 := kind_shape lem rfl
    have lem2 := type_shape tstar (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_datatype_kind wf fh;
    have lem1 := kind_shape lem rfl
    have lem2 := type_shape tstar (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case _ =>
      cases h1; apply Or.inl;
      unfold Ctx.is_ctor; unfold Frame.is_ctor; rw [fh]
  case _ =>
    injection h1 with h1; cases h1;
    have lem := ctx_get_opent_kind wf fh;
    have lem1 := kind_shape lem rfl
    have lem2 := type_shape tstar (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case _ =>
    cases h1; apply Or.inr;
    unfold Ctx.is_insttype; unfold Frame.is_insttype; rw[fh]

theorem cannonical_head :
  Val Γ t ->
  Γ ⊢ t : τ ->
  Γ ⊢ τ : ★ ->
  t.neutral_form = .some (h, ts) ->
  (Γ.is_ctor h ∨ Γ.is_insttype h ∨ OpenVarVal Γ h ts)
:= by
intro vt tJ τJ tnf;
have tshape := Term.neutral_form_law (Eq.symm tnf)
rw[<-tshape] at tJ;
have hJ := inversion_apply_spine tJ;
cases hJ; case _ τ' hJ =>
cases hJ; case _ spTy hJ =>
cases hJ; case _ hJ h3 =>
cases vt
any_goals(solve | cases tnf)
case app h_stable tnf' =>
  cases h_stable
  case _ h_stable =>
   rw[tnf] at tnf'; cases tnf';
   cases hJ; case _ wf gt =>
   have τ'J := spine_type_is_type τJ spTy
   have hJ := Judgment.var wf gt;
   simp at h_stable;
   generalize fh : Γ d@ h = f at *;
   cases f;
   any_goals (solve | cases gt)
   all_goals (unfold Frame.is_stable_red at h_stable; simp at h_stable)
   all_goals (clear h_stable; unfold Frame.get_type at gt; simp at gt; cases gt)
   case _ =>
     have h := ctx_get_var_type wf fh;
     have lem1 := kind_shape h rfl
     have lem2 := type_shape τ'J (by constructor)
     exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
   case _ =>
     have h := ctx_get_datatype_kind wf fh;
     have lem1 := kind_shape h rfl
     have lem2 := type_shape τ'J (by constructor)
     exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
   case _ =>
     apply Or.inl;
     simp; rw[fh]; unfold Frame.is_ctor; simp;
   case _ =>
     have h := ctx_get_opent_kind wf fh
     have lem1 := kind_shape h rfl
     have lem2 := type_shape τ'J (by constructor)
     exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
   case _ =>
     apply Or.inr;
     simp; rw[fh]; unfold Frame.is_insttype; simp;
  case _ ovv =>
    rw[tnf] at tnf'; cases tnf'
    apply Or.inr; apply Or.inr
    assumption

inductive ArrowLike : (T : Term) -> Prop where
| arrowt : ArrowLike (A -t> B)
| allt : ArrowLike (∀[A] B)

inductive LambdaLike (Γ : Ctx Term) : (T : Term) -> Prop where
| lam : LambdaLike Γ (`λ[A] B)
| lamt : LambdaLike Γ (Λ[A] B)
| ctor : ValidHeadVariable t Γ.is_ctor -> LambdaLike Γ t
| insttype : ValidHeadVariable t Γ.is_insttype -> LambdaLike Γ t
| choice :
  LambdaLike Γ t1 ->
  LambdaLike Γ t2 ->
  LambdaLike Γ (t1 ⊕ t2)
| app :
  OpenVarVal Γ h τs ->
  LambdaLike Γ ((#h).apply_spine τs)

@[simp]
abbrev CanonicalLambdaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, τ) =>
       Val Γ t ->
       Γ ⊢ t : τ ->
       Γ ⊢ τ : ★ ->
       ArrowLike τ ->
       LambdaLike Γ t
| .wf => λ () => true

theorem neutral_form_apply_spine :
  (#n).apply_spine τs = t ->
  t.neutral_form = .some (n, τs) := by
intro h; rw[<-h]
induction τs <;> simp at *
sorry


theorem canonical_lambda :
  Judgment v Γ idx ->
  CanonicalLambdaType Γ v idx
:= by
intro j; induction j <;> simp at *
all_goals (intro h1 h2 h3 h4)
any_goals try (solve | cases h1; case _ h1 => cases h1)
any_goals try (solve | cases h3)
case var Γ n T wf gt ih =>
  cases h1; case _ n_stable nnf =>
  simp at nnf; cases nnf; case _ e1 e2 =>
  subst e1; subst e2;
  generalize fh : Γ d@ n = f at *;
  unfold Frame.get_type at gt;
  cases h4
  case arrowt =>
    split at gt;
    any_goals (solve | cases gt)
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
      unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable;
      rw[fh] at n_stable; simp at n_stable
      have wfr := @frame_wf_by_index Γ n wf;
      cases n_stable; case _ n_stable _ =>
      simp at n_stable; rw[fh] at n_stable;
      unfold Frame.is_openm at n_stable; simp at n_stable
    case _ A B _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      replace wfr' := frame_wf_type_implies_kind (A -t> B) wfr
            (by rw[fh]; unfold Frame.get_type; simp)
            (by apply Or.inr; apply Or.inl; simp; rw[fh]; unfold Frame.is_datatype; simp)
      apply LambdaLike.ctor; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_ctor; simp
      have lem : (A -t> B).IsType := type_shape h3 (by constructor)
      exfalso
      have lem' := uniqueness_of_kinds lem wfr' h3; cases lem'
    case _ =>
      constructor
      unfold ValidHeadVariable; exists (n, [])
      constructor <;> simp
      · rw[fh]; unfold Frame.is_ctor; simp
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_opent_kind wf fh;
      cases h;
    case _ =>
      cases n_stable
      case _ h => simp at h; rw[fh] at h; unfold Frame.is_stable_red at h; simp at h
      case _ A B _ h =>
        apply @LambdaLike.app Γ n [] h
    case _ =>
      apply LambdaLike.insttype; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_insttype; simp
    case _ =>
      cases n_stable
      case _ h => simp at h; rw[fh] at h; unfold Frame.is_stable_red at h; simp at h
      case _ h => unfold OpenVarVal at h; simp at h; rw[fh] at h; unfold Frame.is_openm at h; simp at h;
  case allt =>
    split at gt;
    any_goals (solve | cases gt)
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
      unfold Ctx.is_stable_red at n_stable; unfold Frame.is_stable_red at n_stable;
      rw[fh] at n_stable; simp at n_stable
      have wfr := @frame_wf_by_index Γ n wf;
      cases n_stable; case _ n_stable _ =>
      simp at n_stable; rw[fh] at n_stable;
      unfold Frame.is_openm at n_stable; simp at n_stable
    case _ A B _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      replace wfr' := frame_wf_type_implies_kind (∀[A] B) wfr
            (by rw[fh]; unfold Frame.get_type; simp)
            (by apply Or.inr; apply Or.inl; simp; rw[fh]; unfold Frame.is_datatype; simp)
      apply LambdaLike.ctor; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_ctor; simp
      have lem : (∀[A] B).IsType := type_shape h3 (by constructor)
      exfalso
      have lem' := uniqueness_of_kinds lem wfr' h3; cases lem'
    case _ =>
      constructor
      unfold ValidHeadVariable; exists (n, [])
      constructor <;> simp
      · rw[fh]; unfold Frame.is_ctor; simp
    case _ =>
      have wfr := @frame_wf_by_index Γ n wf;
      have h := ctx_get_opent_kind wf fh;
      cases h;
    case _ =>
      cases n_stable
      case _ h => simp at h; rw[fh] at h; unfold Frame.is_stable_red at h; simp at h
      case _ A B _ h =>
        apply @LambdaLike.app Γ n [] h
    case _ =>
      apply LambdaLike.insttype; unfold ValidHeadVariable;
      apply Exists.intro (n, []);
      apply And.intro; simp; simp; rw[fh]; unfold Frame.is_insttype; simp
    case _ =>
      cases n_stable
      case _ h => simp at h; rw[fh] at h; unfold Frame.is_stable_red at h; simp at h
      case _ h => unfold OpenVarVal at h; simp at h; rw[fh] at h; unfold Frame.is_openm at h; simp at h;


case appk Γ f _ _ _ fJ _ _ ih => -- appk bogus case
  cases h1; case _ n ts n_stable ts' =>
  simp at ts'; rw [Option.bind_eq_some_iff] at ts';  cases ts'; case _ w fnf =>
  cases fnf; case _ fnf ts' =>
  cases ts';
  have vf : Val Γ f := by
    constructor
    · assumption
    · cases n_stable;
      case _ => apply Or.inl; assumption
      case _ h =>
        apply Or.inr
        unfold OpenVarVal at h; cases h; case _ h =>
        unfold OpenVarVal; constructor
        · assumption
        · intro T gt;
          replace h := h T gt
          simp at h; omega
  generalize fh : Γ d@ w.fst = f at *;
  have lem := classification_lemma fJ; simp at lem; cases lem;
  case _ h => cases h; case _ k1 k2 =>
    have lem1 := kind_shape k2 rfl
    have lem2 := type_shape h3 (by constructor)
    exfalso; apply Term.is_kind_disjoint_is_type lem1 lem2
  case _ h =>
    cases h; case _ w h =>
    cases h; case _ wk arrk =>
    cases arrk; cases wk;

case lam Γ A t B ih1 ih2 => constructor
case lamt ih1 _ =>
  cases h1
  case _ h => cases h
  case _ => constructor

case app Γ f A B a B' fJ aJ h0 ih1 ih2 =>
  cases h1; case _ n ts n_stable h1 =>
  simp at h1; rw[Option.bind_eq_some_iff] at h1;
  cases h1;  case _ ts' fnf =>
  cases fnf; case _ fnf hts =>
  cases ts'; case _ x sp =>
  simp at hts; cases hts; case _ e1 e2 =>
  subst e1; subst e2
  have h : Val Γ f := Val.app x sp fnf
    (by cases n_stable;
        case _ => apply Or.inl; assumption
        case _ h =>
          apply Or.inr; unfold OpenVarVal at h; simp at h;
          cases h; case _ h =>
          unfold OpenVarVal; simp at *
          constructor
          · assumption
          · intro T gt; replace h := h T gt; omega
    )
  simp at *
  have lem := classification_lemma fJ; simp at lem;
  cases lem;
  case _ h => cases h
  case _ h =>
    cases h; case _ k h =>
    cases h; case _ k h =>
    cases h; case _ aK bK =>
    have arrK := Judgment.arrow aK bK;
    have ih := ih1 h fJ arrK (ArrowLike.arrowt); cases ih;
    case _ h => cases fnf
    case _ h => cases fnf
    case _ h =>
      apply LambdaLike.ctor;
      unfold ValidHeadVariable;
      have fanf := @Term.neutral_form_app f a x sp fnf; symm at fanf;
      apply Exists.intro (x, sp ++ [(.term, a)]);
      apply And.intro; assumption; simp;
      unfold ValidHeadVariable at h; simp at h;
      cases h; case _ h => cases h; case _ fnf' h =>
      rw [fnf] at fnf'; cases fnf'; case _ h =>
      cases h; assumption
    case _ h =>
      apply LambdaLike.insttype;
      unfold ValidHeadVariable;
      have fanf := @Term.neutral_form_app f a x sp fnf; symm at fanf;
      apply Exists.intro (x, sp ++ [(.term, a)]);
      apply And.intro; assumption; simp;
      unfold ValidHeadVariable at h; simp at h;
      cases h; case _ h => cases h; case _ fnf' h =>
      rw [fnf] at fnf'; cases fnf'; case _ h =>
      cases h; assumption
    case _ => cases fnf
    case _ n τs _ =>
      simp at *;
      have ih := ih1 h fJ arrK (by constructor)
      generalize tdef : (#n).apply_spine τs = t at *
      have lem := @Term.apply_spine_term_extend t τs a #n (Eq.symm tdef); rw[lem]
      have lem := neutral_form_apply_spine tdef; rw[lem] at fnf; cases fnf;
      apply LambdaLike.app
      cases n_stable;
      case _ h _ _ =>
        unfold OpenVarVal at h; simp at h; cases h;
        case _ h' h _ => have lem := Frame.is_openm_implies_not_is_stable_red h; exfalso; apply lem h'
      case _ => assumption

case _ Γ f A B a B' fJ aJ _ ih1 ih2 =>
  cases h1; case _ n ts n_stable h1 =>
  simp at h1; rw[Option.bind_eq_some_iff] at h1;
  cases h1;  case _ ts' fnf =>
  cases fnf; case _ fnf hts =>
  cases ts'; case _ x sp =>
  simp at hts; cases hts; case _ e1 e2 =>
  subst e1; subst e2
  have h : Val Γ f := Val.app x sp fnf
    (by cases n_stable;
        case _ => apply Or.inl; assumption
        case _ h =>
          apply Or.inr; unfold OpenVarVal at h; simp at h;
          cases h; case _ h =>
          unfold OpenVarVal; simp at *
          constructor
          · assumption
          · intro T gt; replace h := h T gt; omega
    )

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
    case _ h => cases fnf
    case _ h => cases fnf
    case _ h =>
        apply LambdaLike.ctor;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_appt f a x sp fnf; symm at fanf;
        apply Exists.intro (x, sp ++ [(.type, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; assumption;
    case _ h =>
        apply LambdaLike.insttype;
        unfold ValidHeadVariable;
        have fanf := @Term.neutral_form_appt f a x sp fnf; symm at fanf;
        apply Exists.intro (x, sp ++ [(.type, a)]);
        apply And.intro; assumption; simp;
        unfold ValidHeadVariable at h; simp at h;
        cases h; case _ h => cases h; case _ fnf' h =>
        rw [fnf] at fnf'; cases fnf'; case _ h =>
        cases h; assumption;
    case _ => cases fnf
    case _ hd tl _ =>
      simp at *;
      have ih := ih1 h fJ arrK (by constructor)
      generalize tdef : (#hd).apply_spine tl = t at *
      have lem := @Term.apply_spine_type_extend t tl a #hd (Eq.symm tdef); rw[lem]
      have lem := neutral_form_apply_spine tdef; rw[lem] at fnf; cases fnf;
      apply LambdaLike.app
      cases n_stable;
      case _ h _ _ =>
        unfold OpenVarVal at h; simp at h; cases h;
        case _ h' h _ => have lem := Frame.is_openm_implies_not_is_stable_red h; exfalso; apply lem h'
      case _ => assumption

case refl ih2 => cases h4
case choice j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
  cases h1; case _ h => cases h
  case _ v1 v2 =>
    replace ih3 := ih3 v1 j3 h3 h4
    replace ih4 := ih4 v2 j4 h3 h4
    apply LambdaLike.choice ih3 ih4
@[simp]
abbrev CanonicalDatatypeLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> (JudgmentArgs v) -> Prop
| .prf => λ (t, τ) =>
  Γ ⊢ t : τ ->
  Val Γ t ->
  ValidHeadVariable τ Γ.is_datatype ->
  (ValidHeadVariable t Γ.is_ctor) ∨ (∃ t1 t2 : Term, t = (t1 ⊕ t2))
| .wf => λ _ => true

theorem canonical_datatype_lemma :
  Judgment v Γ idx ->
  CanonicalDatatypeLemmaType Γ v idx := by
intro j
induction j <;> simp at *
all_goals (intro h1 h2)
all_goals (try cases h2; case _ h2 => simp at h2)
all_goals (try case _ => intro h; cases h; case _ h => cases h; case _ h _ => simp at h)
case var => intro h; sorry
case appk => sorry
case app => sorry
case appt => sorry


theorem canonical_datatype :
  Γ ⊢ t : T ->
  Val Γ t ->
  ValidHeadVariable T Γ.is_datatype ->
  (ValidHeadVariable t Γ.is_ctor) ∨ (∃ t1 t2 : Term, t = (t1 ⊕ t2)) := by
intro tJ tv vhv
have lem := canonical_datatype_lemma tJ
simp at lem; replace lem := lem tJ tv vhv
cases lem;
case _ lem =>
  apply Or.inl;
  cases lem; case _ x lem =>
  cases lem; case _ lem _ =>
  unfold ValidHeadVariable;
  exists x
case _ lem => apply Or.inr; assumption
