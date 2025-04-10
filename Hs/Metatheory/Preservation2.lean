import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import SystemFD.Algorithm.Soundness2

set_option maxHeartbeats 500000

-- Says how the shape of the core context changes with Hs Ctx
@[aesop safe [constructors, cases]]
inductive CompileCtx : Ctx HsTerm -> Ctx Term -> Prop where
| nil : CompileCtx [] []
| empty :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  CompileCtx (.empty :: Γ) (.empty :: Γ')
| kind :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢κ A : `□) ->
  compile_kind Γ A `□ j1 = .some A' ->
  CompileCtx (.kind A :: Γ) (.kind A' :: Γ')
| datatype :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢κ A : `□) ->
  compile_kind Γ A `□ j1 = .some A' ->
  CompileCtx (.datatype A :: Γ) (.datatype A' :: Γ')
| type :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.type A :: Γ) (.type A' :: Γ')
| ctor :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.ctor A :: Γ) (.ctor A' :: Γ')
| term :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★)  ->
  (j2 : Γ ⊢t t : τ) ->
  compile_type Γ A `★ j = .some A' ->
  compile_term Γ t τ j2 = .some t' ->
  CompileCtx (.term A t :: Γ) (.term A' t' :: Γ')
| openm :
  ⊢s Γ ->
  ⊢ Γ' ->
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.openm A :: Γ) (.openm A' :: Γ')

theorem ctx_shift (Γ : Ctx HsTerm) :
  (f :: Γ)d@(n + 1) = .datatype k ->
  ∃ k', (Γ d@ n) = .datatype k' := by
intro h;
unfold dnth at h; unfold Frame.apply at h;
generalize fh : Γ d@n = f at *;
cases f;
all_goals (simp at h)
case _ a => exists a

theorem compile_ctx_shape :
  CompileCtx Γ Γ' ->
  (Γ d@ x) = .datatype k ->
  ∃ k', (Γ' d@ x) = .datatype k' := by
intro cc h;
induction cc;
case _ => cases h
case _ Γ Γ' wf wf' cc ih =>
  cases x;
  case _ => unfold dnth at h; cases h
  case _ =>
    have lem := ctx_shift Γ h
    cases lem; case _ lem =>
    sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry


theorem compile_preserves_kinds :
  ⊢ Γ' ->
  (j : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j = .some t' ->
  Γ' ⊢ t' : .kind := by
 intro cc j c;
 induction Γ, t, τ, j using compile_kind.induct generalizing t'
 all_goals try (cases e)
 case _ =>
   unfold compile_kind at c; cases c;
   case _ =>
     apply Judgment.ax; assumption;
 case _ j1 j2 ih1 ih2 =>
   unfold compile_kind at c; simp at c;
   rw[Option.bind_eq_some] at c;
   cases c; case _ w1 c1 =>
   cases c1; case _ c1 c2 =>
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ w2 c2 =>
   cases c2; case _ c2 c3 =>
   cases c3;
   have ih1' := ih1 c1;
   have ih2' := ih2 c2;
   apply Judgment.allk;
   apply ih1';
   apply ih2'

theorem compile_preserves_kind_indices :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  CompileCtx Γ Γ' ->
  (Γ d@ x).is_datatype || (Γ d@ x).is_kind ->
  (j : Γ ⊢κ k : s) ->
  (Γ d@ x).get_type = .some k ->
  compile_kind Γ k s j = .some k' ->
  (Γ' d@ x).get_type = .some k' := by
intro h' cc t j gt c;
sorry
-- induction Γ, k, s, j using compile_kind.induct generalizing k'
-- case _ Γ wf =>
--   unfold compile_kind at c; cases c;
--   induction cc generalizing x <;> simp at *
--   case _ =>
--     cases t;
--     case _ t => cases t
--     case _ t => cases t
--   case _ ih =>
--     cases t;
--     case _ t =>
--       cases wf; case _ wf =>
--       have ih' := @ih (x - 1) sorry sorry sorry
--       sorry
--     case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
--   case _ => sorry
-- case _ => sorry



-- have lem := well_sorted_kind_inversion j; cases lem
-- induction x generalizing Γ Γ' <;> simp at *;
-- case _ =>
--   unfold Frame.get_type at gt;
--   cases t;
--   case _ h =>
--     have lem := datatype_indexing_exists h;
--     cases lem; case _ w h =>
--     rw [h] at gt; simp at gt; cases gt; unfold Frame.get_type;
--     cases cc <;> cases h; unfold dnth; unfold Frame.apply; simp;
--     case _ wf wf' cc ja ca =>
--     have lem1 := hs_weaken_kind (HsJudgment.wfdatatype ja wf) ja
--     have lem2 := weaken_compile_kind ja lem1 ca
--     apply compile_kind_uniqueness h' lem1 j lem2 c;
--   case _ h =>
--     have lem := kind_indexing_exists h;
--     cases lem; case _ w h =>
--     rw [h] at gt; simp at gt; cases gt; unfold Frame.get_type;
--     cases cc <;> cases h; unfold dnth; unfold Frame.apply; simp;
--     case _ wf wf' cc ja ca =>
--     have lem1 := hs_weaken_kind (HsJudgment.wfkind ja wf) ja
--     have lem2 := weaken_compile_kind ja lem1 ca
--     apply compile_kind_uniqueness h' lem1 j lem2 c;
-- case _ ih =>
--   have ih' := @ih (.empty :: Γ) (.empty :: Γ')
--   sorry


-- theorem compile_preserves_kind_shape :
--   ⊢ Γ' ->
--   (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
--   (j1 : Γ ⊢κ A : `□) ->
--   (j2 : Γ ⊢κ B : `□) ->
--   (j3 : Γ ⊢κ (A `-k> B) : `□) ->
--   compile_kind Γ A `□ j1 = .some A' ->
--   compile_kind Γ B `□ j2 = .some B' ->
--   compile_kind Γ (A `-k> B) `□ j3 = .some t' ->
--   t' = (A' -k> B') := by
-- intro wf h j1 j2 j3 c1 c2 c3;
-- have c3' := c3;
-- unfold compile_kind at c3; cases j3;
-- case _ ja jb =>
-- simp at c3;
-- rw[Option.bind_eq_some] at c3;
-- cases c3; case _ w1 c3 =>
-- cases c3; case _ c3 c4 =>
-- rw[Option.bind_eq_some] at c4;
-- cases c4; case _ w2 c4 =>
-- cases c4; case _ c4 c5 =>
-- cases c5;
-- have u := kinds_compiling_uniqueness h j1 ja c1 c3; cases u;
-- have u := kinds_compiling_uniqueness h j2 jb c2 c4; cases u;
-- simp

theorem compile_preserves_types :
  CompileCtx Γ Γ' ->
  ⊢ Γ' ->
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j2 : Γ ⊢κ k : `□) ->
  compile_kind Γ k `□ j2 = .some k' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  Γ' ⊢ τ' : k' := by
intro cc wf h j1 c1 j2 c2;
induction Γ, τ, k, j2 using compile_type.induct generalizing Γ' τ' k'
all_goals (unfold compile_type at c2; simp at c2)
case _ Γ T x wf' test gt j =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w c2 =>
  cases c2; case _ c2 e =>
  cases e;
  have lem := kinds_have_unique_judgments h j j1; cases lem;
  rw[c1] at c2; cases c2;
  have lem := Eq.symm (compile_preserves_kind_indices h cc test j (Eq.symm gt) c1)
  apply Judgment.var; assumption; assumption

case _ Γ B f A a  h1 h2 ja jb ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 c4 =>
  rw[Option.bind_eq_some] at c4;
  cases c4; case _ w3 c4 =>
  cases c4; case _ c4 c5 =>
  rw[Option.bind_eq_some] at c5;
  cases c5; case _ w4 c5 =>
  cases c5; case _ c5 e =>
  cases e;
  apply Judgment.appk;
  case _ =>
    have u := compile_kind_uniqueness h j1 jb c1 c3; cases u;
    have h' : compile_kind Γ (A `-k> B) `□ (ja.arrowk jb) = some (w1 -k> k') := by
      unfold compile_kind; simp;
      rw[Option.bind_eq_some];
      exists w1; apply And.intro
      case _ => assumption
      case _ => rw[Option.bind_eq_some]; simp; assumption
    have ih1' := @ih1 Γ' (w1 -k> k') w3 cc wf (HsJudgment.arrowk ja jb) h' c4
    apply ih1';
  case _ =>
    apply @ih2 Γ' w1 w4 cc wf ja c2 c5

case _ h1 h2 ih1 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e; unfold compile_kind at c1; cases j1;
  simp at c1; cases c1;
  apply Judgment.allt;
  apply compile_preserves_kinds wf h1 c2;
  apply @ih1 (.kind w1 :: Γ') ★ w2 _ _ _ _ c3
  case _ => apply CompileCtx.kind; assumption; assumption; assumption; assumption
  case _ => apply Judgment.wfkind; apply compile_preserves_kinds wf h1 c2; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfkind; assumption; assumption
  case _ => unfold compile_kind; rfl

case _ A B j1' j2' ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have lem1 := compile_preserves_kinds wf j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl

  apply @ih2 (.empty::Γ') ★ w2 _ _ _ _ c3;
  case _ => apply CompileCtx.empty; assumption; assumption; assumption
  case _ => apply Judgment.wfempty; assumption;
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl

case _ j1 _ j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have lem1 := compile_preserves_kinds wf j1 c1;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  case _ tl1 tl2 _ =>
  apply Judgment.arrow;
  apply @ih1 Γ' ★ w1 cc wf _ _ c2;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 (.empty::Γ') ★ w2 _ _ _ _ c3
  case _ => apply CompileCtx.empty; assumption; assumption; assumption
  case _ => apply Judgment.wfempty; assumption
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl


@[simp]
abbrev CompilePreservesTypeShapeAll :  (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Prop
| .type => λ Γ => λ (τ, k) => ∀ wA wτ cτ,
  τ = (`∀{wA} wτ) ->
  k = `★ ->
  (j3 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j3 = .some cτ ->
  ∃ A' τ', cτ = ∀[A']τ'
| _ => λ _ => λ _ => true

theorem comile_preserves_type_shape_all_lemma :
  HsJudgment v Γ idx -> CompilePreservesTypeShapeAll v Γ idx
 := by
intro j; induction j <;> simp at *;
intro wA wτ cτ e1 e2 j3 c3;
cases j3; case _ hka hkb =>
unfold compile_type at c3; simp at c3;
rw[Option.bind_eq_some] at c3;
cases c3; case _ A' c3 =>
cases c3; case _ cA c4 =>
rw[Option.bind_eq_some] at c4;
cases c4; case _ B' c4 =>
cases c4; case _ cB e =>
cases e; simp;

theorem compile_preserves_type_shape_all :
  (j : Γ ⊢τ (`∀{A}τ) : `★) ->
  compile_type Γ (`∀{A}τ) `★ j = .some cτ ->
  ∃ A' τ', cτ = ∀[A']τ' := by
intro j c;
have lem := comile_preserves_type_shape_all_lemma j; simp at lem;
apply @lem A τ cτ rfl rfl j c


theorem compile_preserves_type_indices :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  CompileCtx Γ Γ' ->
  (Γ d@ x).is_ctor || (Γ d@ x).is_term || (Γ d@ x).is_type ->
  (j : Γ ⊢τ T : k) ->
  (Γ d@ x).get_type = .some T ->
  compile_type Γ T k j = .some T' ->
  (Γ' d@ x).get_type = .some T' := by sorry

theorem compile_preserves_terms :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  CompileCtx Γ Γ' ->
  ⊢ Γ' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  (j2 : Γ ⊢t t : τ) ->
  compile_term Γ t τ j2 = .some t' ->
  Γ' ⊢ t' : τ' := by
intro h cc wf j1 c1 j2 c2;
induction Γ, t, τ, j2 using compile_term.induct generalizing Γ' t' τ' k
all_goals (unfold compile_term at c2; simp at c2)
case _ wf test gt =>
     cases c2;
     apply Judgment.var;
     assumption;
     have lem := compile_preserves_type_indices h cc test j1 (Eq.symm gt) c1;
     apply Eq.symm lem

case _ Γ A t B j1' j2 j3 ih1 => -- lam
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ A' c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ B' c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ t' c4 =>
 cases c4; case _ c4 e =>
 cases e;
 -- have uniq := types_have_unique_kinds j1 j3; subst uniq;
 unfold compile_type at c1; cases j1; simp at c1;
 rw[Option.bind_eq_some] at c1;
 cases c1; case _ x1 c1' =>
 cases c1'; case _ c1' c2' =>
 rw[Option.bind_eq_some] at c2';
 cases c2'; case _ B' c2' =>
 cases c2'; case _ c2' e =>
 cases e; case _ ja jb =>
 have cc' : CompileCtx (.type A :: Γ) (.type A' :: Γ') := by
   apply CompileCtx.type;
   apply hs_judgment_ctx_wf .type j1'
   apply wf
   apply cc
   apply c2
 have wf' : ⊢ (.type A' :: Γ') := by
   apply Judgment.wftype
   apply compile_preserves_types cc wf h _ _ j1' c2
   case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type ja)
   case _ => unfold compile_kind; rfl
   assumption
 have lem := compile_type_uniqueness h j1' ja c2 c1'; cases lem;
 apply Judgment.lam;
 apply compile_preserves_types cc wf h _ _ ja c1'
 case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type ja)
 case _ => unfold compile_kind; rfl
 case _ =>
   have ih1' := @ih1 (.type A' :: Γ') `★ B' t' cc' wf'
   sorry
 apply compile_preserves_types cc wf h _ _ _ _
 case _ => apply `★;
 case _ => apply (A → B)
 case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type ja)
 case _ => unfold compile_kind; rfl
 case _ => apply HsJudgment.arrow; assumption; assumption
 case _ =>
   unfold compile_type; simp;
   rw[Option.bind_eq_some]; exists A';
   apply And.intro; assumption;
   rw[Option.bind_eq_some]; exists B';

case _ h1 h2 ih1 ih2 =>
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ wt1 c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ wt2 c3 =>
 cases c3; case _ c3 e =>
 cases e;
 apply Judgment.app;
 sorry
 case _ =>
   have ih2' := @ih2 Γ' `★
   sorry
 sorry
 sorry
 sorry

case _ =>
 sorry
case _ =>
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ wt1 c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ wt2 c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ wt3 c4 =>
 cases c4; case _ c4 c5 =>
 rw[Option.bind_eq_some] at c5;
 cases c5; case _ wt4 c5 =>
 cases c5; case _ c5 e =>
 cases e;
 apply Judgment.ite;
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry

-- implicits
case _ Γ t A τ e h1 h2 h3 h4 ih => -- implicitAllE
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ wτ c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ wA c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ wt c4 =>
 cases c4; case _ c4 c5 =>
 rw[Option.bind_eq_some] at c5;
 cases c5; case _ we c5 =>
 cases c5; case _ c5 e =>
 cases e;
 have lem := compile_preserves_type_shape_all h1 c2;
 cases lem; case _ A' lem =>
 cases lem; case _ τ' lem =>
 cases lem;
 apply Judgment.appt;
 case _ => --
   have ih' := @ih Γ' `★ (∀[A']τ') wt cc wf h1 c2 c4;
   apply ih'
 case _ =>
   have h' := compile_preserves_types cc wf h h2 c3 h4 c5
   unfold compile_type at c2; cases h1; simp at c2;
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ wA' c2' =>
   cases c2'; case _ c2' c3' =>
   rw[Option.bind_eq_some] at c3';
   cases c3'; case _ wτ' c3' =>
   cases c3'; case _ c3' e  =>
   cases e; case _ h2' _ =>
   have lem := compile_kind_uniqueness h h2 h2' c3 c2'; cases lem;
   assumption
 case _ =>
   have h' := compile_preserves_types cc wf h h2 c3 h4 c5
   unfold compile_type at c2; cases h1; simp at c2;
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ wA' c2' =>
   cases c2'; case _ c2' c3' =>
   rw[Option.bind_eq_some] at c3';
   cases c3'; case _ wτ' c3' =>
   cases c3'; case _ c3' e  =>
   cases e; case _ h2' j1' =>
   have lem := compile_kind_uniqueness h h2 h2' c3 c2'; cases lem;
   have j1'' := hs_beta_kind_type j1' h4; simp at j1'';
   have u := types_have_unique_kinds j1 j1''; cases u;
   have u := types_have_unique_judgments h j1 j1''; cases u;
   have lem := compile_beta_kind_type j1' c3' h4 c5 j1'';
   have lem1 : compile_type Γ ([Subst.Action.su e::I]τ) ([Subst.Action.su e::I]`★) j1'' = compile_type Γ ([Subst.Action.su e::I]τ) `★ j1'' := by rfl
   rw[lem1] at lem;
   rw[c1] at lem; cases lem; rfl

case _ Γ t A τ j1' j2 j3 ih =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ wt c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ wA c3 =>
  cases c3; case _ c3 e =>
  cases e;
  have u := all_kind_inversion j1; cases u;
  cases j1; case _ ja' j1 =>
  unfold compile_type at c1; simp at c1;
  rw[Option.bind_eq_some] at c1;
  cases c1; case _ wA' c1 =>
  cases c1; case _ c1 c2' =>
  rw[Option.bind_eq_some] at c2';
  cases c2'; case _ wt' c2' =>
  cases c2'; case _ c2' e =>
  cases e;
  have u := kinds_have_unique_judgments h ja' j2; cases u;
  rw[c1] at c3; cases c3;
  have cc' : CompileCtx (.kind A::Γ) (.kind wA :: Γ') := by
    apply CompileCtx.kind _ wf cc;
    case _ => apply c1
    apply hs_judgment_ctx_wf .kind j2
  have lem : ⊢ (.kind wA :: Γ') := by
    apply Judgment.wfkind;
    apply compile_preserves_kinds wf j2 c1; assumption
  apply Judgment.lamt;
  apply compile_preserves_kinds wf j2 c1
  apply @ih (Frame.kind wA :: Γ') `★ wt' wt cc' lem j1 c2' c2;
  case _ =>
    apply Judgment.allt;
    apply compile_preserves_kinds wf j2 c1;
    apply compile_preserves_types cc' lem h _ _ j1 c2'
    case _ =>
      apply HsJudgment.ax;
      apply HsJudgment.wfkind; assumption
      apply (hs_judgment_ctx_wf .kind j2)
    case _ =>
      unfold compile_kind; rfl;

case _ => sorry
case _ => sorry

---------------------------------------------
-- Contexts
--------------------------------------------

theorem compile_preserves_wf Γ :
  ⊢s Γ -> (Η : HsCtx Γ) -> compile_ctx Η = .some Γ' -> ⊢ Γ' := by
intro wf h cc;
induction h generalizing Γ';
case _ =>
  unfold compile_ctx at cc; cases cc;
  apply Judgment.wfnil;
case _ ih =>
  cases wf; case _ wf =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  cases cc2;
  apply Judgment.wfempty;
  apply wf_ctx_sound cc1;
case _ j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ w2 cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  apply Judgment.wfkind;
  apply compile_preserves_kinds _ j cc2;
  case _ => apply @ih w wf cc
  apply @ih w wf cc
case _ j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ w2 cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  apply Judgment.wfdatatype;
  apply compile_preserves_kinds _ j cc2;
  case _ => apply @ih w wf cc
  apply @ih w wf cc
case _ j ih =>
  cases wf; case _ wf jk =>
  unfold compile_ctx at cc; simp at cc;
  rw[Option.bind_eq_some] at cc;
  cases cc; case _ w cc =>
  cases cc; case _ cc cc1 =>
  rw[Option.bind_eq_some] at cc1;
  cases cc1; case _ w1 cc1 =>
  cases cc1; case _ cc1 cc2 =>
  rw[Option.bind_eq_some] at cc2;
  cases cc2; case _ w2 cc2 =>
  cases cc2; case _ cc2 cc3 =>
  cases cc3; cases w1;
  have lem := @ih w wf cc
  apply Judgment.wftype;
  sorry -- apply compile_preserves_types lem sorry
  apply @ih w wf cc
  -- apply compile_preserves_types _ j cc2;
  -- case _ => apply @ih w wf cc
  --

case _ => sorry
case _ => sorry


theorem cc_soundness Γ : ⊢s Γ -> (Η : HsCtx Γ) -> compile_ctx Η = .some Γ' -> CompileCtx Γ Γ'
  := by
intro wf h j
induction h using compile_ctx.induct generalizing Γ'
case _ =>
  unfold compile_ctx at j; cases j;
  constructor;
case _ Γ Η ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 e =>
  cases e; cases wf; case _ wf =>
  apply CompileCtx.empty;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
case _ Γ k Η jk ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 j2 =>
  rw[Option.bind_eq_some] at j2;
  cases j2; case _ w2 j2 =>
  cases j2; case _ j2 e =>
  cases e; cases wf; case _ wf jk' =>
  apply CompileCtx.kind;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
  assumption
case _ Γ k Η jk ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 j2 =>
  rw[Option.bind_eq_some] at j2;
  cases j2; case _ w2 j2 =>
  cases j2; case _ j2 e =>
  cases e; cases wf; case _ wf jk' =>
  apply CompileCtx.datatype;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
  assumption
case _  Γ k Η _ ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 j2 =>
  rw[Option.bind_eq_some] at j2;
  cases j2; case _ w2 j2 =>
  cases j2; case _ j2 e =>
  cases e; cases wf; case _ wf jk' =>
  apply CompileCtx.type;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
  assumption
case _  Γ k Η _ ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 j2 =>
  rw[Option.bind_eq_some] at j2;
  cases j2; case _ w2 j2 =>
  cases j2; case _ j2 e =>
  cases e; cases wf; case _ wf _ vh =>
  apply CompileCtx.ctor;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
  assumption
case _  Γ k Η _ ih =>
  unfold compile_ctx at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ w j =>
  cases j; case _ j j1 =>
  rw[Option.bind_eq_some] at j1;
  cases j1; case _ w1 j1 =>
  cases j1; case _ j1 j2 =>
  rw[Option.bind_eq_some] at j2;
  cases j2; case _ w2 j2 =>
  cases j2; case _ j2 e =>
  cases e; cases wf; case _ wf jk =>
  apply CompileCtx.openm;
  assumption
  apply compile_preserves_wf Γ wf Η j
  apply ih wf j
  assumption

-- theorem cc_completeness Γ : ⊢s Γ -> (Η : HsCtx Γ) -> CompileCtx Γ Γ' -> compile_ctx Η = .some Γ'
--   := by
-- intro wf h cc
-- induction cc;
-- case _ =>
--   cases h; unfold compile_ctx; rfl;
-- case _ =>
--   cases h; cases wf; case _ Γ Γ' _ wf' cc ih h wf =>
--   unfold compile_ctx; simp
--   rw[Option.bind_eq_some];
--   exists Γ'; apply And.intro;
--   apply ih wf
--   rw[Option.bind_eq_some];
--   exists (); apply And.intro;
--   sorry
--   simp
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry

theorem compile_preserves_term_indices :
  ⊢ Γ' ->
  (j1 : Γ ⊢t `#x : T) ->
  compile_type Γ T k j = .some T' ->
  (Γ' d@ x).get_type = .some T' := by
sorry
