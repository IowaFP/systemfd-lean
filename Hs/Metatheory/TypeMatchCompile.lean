import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import Hs.Metatheory.Preservation1
import SystemFD.Algorithm.Soundness2

theorem compile_preserves_type_neutral_form :
  ⊢ Γ' ->
  (j : Γ ⊢τ t : k) ->
  compile_type Γ t k j = .some t' ->
  t.neutral_form = .some (h, sp) ->
  ∃ h' sp', t'.neutral_form = .some (h', sp') := by
intro wf j ct tnf;
induction Γ, t, k, j using compile_type.induct generalizing Γ' t' h sp
case _ x _ _ _ _ =>
  unfold compile_type at ct; simp at ct;
  rw[Option.bind_eq_some] at ct;
  cases ct; case _ k ct =>
  cases ct; case _ ct e =>
  cases e; exists x; exists []
case _ a _ _ _ _ ih _ =>
  unfold compile_type at ct; simp at ct;
  rw[Option.bind_eq_some] at ct;
  cases ct; case _ A' ct =>
  cases ct; case _ ct ct1 =>
  rw[Option.bind_eq_some] at ct1;
  cases ct1; case _ B' ct1 =>
  cases ct1; case _ ct1 ct2 =>
  rw[Option.bind_eq_some] at ct2;
  cases ct2; case _ f' ct2 =>
  cases ct2; case _ ct2 ct3 =>
  rw[Option.bind_eq_some] at ct3;
  cases ct3; case _ a' ct3 =>
  cases ct3; case _ ct3 e =>
  cases e
  unfold HsTerm.neutral_form at tnf; simp at tnf;
  rw[Option.bind_eq_some] at tnf;
  cases tnf; case _ nf tnf =>
  cases tnf; case _ fnf e =>
  cases e;
  have ih' := @ih Γ' f' nf.1 nf.snd wf ct2 fnf
  cases ih'; case _ h' ih' =>
  cases ih'; case _ sp' ih' =>
  exists h'; exists (sp' ++ [( SpineVariant.kind, a') ]);
  unfold Term.neutral_form; simp;
  rw[Option.bind_eq_some];
  exists (h', sp');
all_goals (cases tnf)

-- theorem compile_preserves_term_neutral_form :
--   ⊢ Γ' ->
--   (j1 : Γ ⊢τ A : `★) ->
--   (j2 : Γ ⊢t t : A) ->
--   compile_term Γ t A j2 = .some t' ->
--   t.neutral_form = .some (h, sp) ->
--   ∃ h' sp', t'.neutral_form = .some (h', sp') := by
-- intro wf h1 ht ct tnf;
-- induction Γ, t, A, ht using compile_term.induct generalizing Γ' t' h sp <;> simp at *
-- all_goals try (cases tnf)
-- case _ x _ _ _ e1 e2 =>
--   cases e1; cases e2
--   exists x; exists [];
--   unfold compile_term at ct; cases ct; rfl
-- case _ Γ t1 A B t2 j1 j2 j3 j4 ih _ =>
--   rw[Option.bind_eq_some] at tnf;
--   cases tnf; case _ nf tnf =>
--   cases tnf; case _ tnf e =>
--   cases e;
--   unfold compile_term at ct; simp at ct;
--   rw[Option.bind_eq_some] at ct;
--   cases ct; case _ AB' ct =>
--   cases ct; case _ ct ct1 =>
--   rw[Option.bind_eq_some] at ct1;
--   cases ct1; case _ A' ct1 =>
--   cases ct1; case _ ct1 ct2 =>
--   rw[Option.bind_eq_some] at ct2;
--   cases ct2; case _ B' ct2 =>
--   cases ct2; case _ ct2 ct3 =>
--   rw[Option.bind_eq_some] at ct3;
--   cases ct3; case _ t1' ct3 =>
--   cases ct3; case _ ct3 ct4 =>
--   rw[Option.bind_eq_some] at ct4;
--   cases ct4; case _ t2' ct4 =>
--   cases ct4; case _ ct4 e =>
--   cases e;
--   have ih' := @ih Γ' t1' nf.1 nf.2 wf (extract_typing j1) ct3 tnf
--   cases ih'; case _ h' ih' =>
--   cases ih'; case _ sp' ih' =>
--   exists h'; exists (sp' ++ [(.term, t2')]);
--   simp; rw[Option.bind_eq_some];
--   exists (h', sp');
-- case _ Γ t A τ e j1 j2 j3 j4 j5 ih =>
--   unfold compile_term at ct; simp at ct
--   rw[Option.bind_eq_some] at ct;
--   cases ct; case _ Aτ' ct =>
--   cases ct; case _ ct ct1 =>
--   rw[Option.bind_eq_some] at ct1;
--   cases ct1; case _ A' ct1 =>
--   cases ct1; case _ ct1 ct2 =>
--   rw[Option.bind_eq_some] at ct2;
--   cases ct2; case _ t' ct2 =>
--   cases ct2; case _ ct2 ct3 =>
--   rw[Option.bind_eq_some] at ct3;
--   cases ct3; case _ a' ct3 =>
--   cases ct3; case _ ct3 e =>
--   cases e;

--   sorry
-- case _ => sorry
-- case _ => sorry
-- case _ => sorry

theorem compile_preserves_vhv_types test σtest :
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jT : Γ ⊢τ T : `★) ->
 compile_type Γ T `★ jT = .some T' ->
 HsValidHeadVariable T test ->
 ValidHeadVariable T' σtest := by sorry


theorem compile_preserves_vhv_terms test σtest :
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jT : Γ ⊢t T : τ) ->
 compile_term Γ T τ jT = .some T' ->
 HsValidHeadVariable T test ->
 ValidHeadVariable T' σtest := by sorry

theorem compile_stable_match :
 (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jA : Γ ⊢τ A : `★) ->
 compile_type Γ A `★ jA = .some A' ->
 (jR : Γ ⊢τ R : `★) ->
 compile_type Γ R `★ jR = .some R' ->
 StableHsTypeMatch Γ A R -> StableTypeMatch Γ' A' R' := by
intro h cc wf jA cA jR cR stm;
induction stm generalizing Γ' A' R';
case _ R Γ vhv =>
  have u := compile_type_uniqueness h jA jR cA cR; cases u
  apply StableTypeMatch.refl;
  apply compile_preserves_vhv_types Γ.is_stable Γ'.is_stable cc wf jR cR vhv;
case _ R Γ B A vhv stm ih =>
  have lem := compile_preserves_type_shape_arrow jA cA;
  cases lem; case _ A' lem =>
  cases lem; case _ B' lem =>
  cases lem; case _ jA' lem =>
  cases lem; case _ jB' lem =>
  cases lem; case _ e lem =>
  subst e
  cases lem; case _ cA' cB' =>
  apply StableTypeMatch.arrow;
  apply compile_preserves_vhv_types Γ.is_stable Γ'.is_stable cc wf jR cR vhv
  have lem := weaken_compile_type h jR cR (HsFrameWf.empty (hs_judgment_ctx_wf .type jA')) (hs_weaken_empty_type jR)
  apply @ih (.empty :: Γ') B' ([S]R') _ jB' cB' (hs_weaken_empty_type jR) lem
  case _ => apply Judgment.wfempty wf

case _ R Γ B A vhv stm ih =>
  have lem := compile_preserves_type_shape_farrow jA cA;
  cases lem; case _ A' lem =>
  cases lem; case _ B' lem =>
  cases lem; case _ jA' lem =>
  cases lem; case _ jB' lem =>
  cases lem; case _ e lem =>
  subst e
  cases lem; case _ cA' cB' =>
  apply StableTypeMatch.arrow;
  apply compile_preserves_vhv_types Γ.is_stable Γ'.is_stable cc wf jR cR vhv
  have lem := weaken_compile_type h jR cR (HsFrameWf.empty (hs_judgment_ctx_wf .type jA')) (hs_weaken_empty_type jR)
  apply @ih (.empty :: Γ') B' ([S]R') _ jB' cB' (hs_weaken_empty_type jR) lem
  case _ => apply Judgment.wfempty wf

case _ R Γ A B vhv stm ih =>
  have lem := compile_preserves_type_shape_all jA cA;
  cases lem; case _ A' lem =>
  cases lem; case _ B' e =>
  subst e
  case _ cA' cB' =>
  apply StableTypeMatch.all;
  apply compile_preserves_vhv_types Γ.is_stable Γ'.is_stable cc wf jR cR vhv
  unfold compile_type at cA; cases jA; simp at cA; case _ jA jB =>
  rw[Option.bind_eq_some] at cA;
  cases cA; case _ A' cA =>
  cases cA; case _ cA cB =>
  rw[Option.bind_eq_some] at cB;
  cases cB; case _ B' cB =>
  cases cB; case _ cB e =>
  cases e;
  have lem := weaken_compile_type h jR cR
                (HsFrameWf.kind jA)
                (hs_weaken_kind_type jA jR)
  apply @ih (.kind A' :: Γ') B' ([S]R') _ jB cB (hs_weaken_kind_type jA jR) lem
  apply Judgment.wfkind; apply compile_preserves_kinds wf jA cA; apply wf

theorem compile_prefix_match :
 (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
 (∀ v, CompileCtxPred v) ->
 ⊢ Γ' ->
 (jA : Γ ⊢τ A : `★) ->
 compile_type Γ A `★ jA = .some A' ->
 (jR : Γ ⊢τ R : `★) ->
 compile_type Γ R `★ jR = .some R' ->
 (jT : Γ ⊢τ T : `★) ->
 compile_type Γ T `★ jT = .some T' ->
 PrefixHsTypeMatch Γ A R T -> PrefixTypeMatch Γ' A' R' T' := by
intro h cc wf jA cA jR cR jT cT ptm;
induction ptm generalizing Γ' A' R' T'
case _ Γ T vhv =>
  have u := compile_type_uniqueness h jR jT cR cT; cases u
  apply PrefixTypeMatch.refl;
  apply compile_preserves_vhv_types Γ.is_stable Γ'.is_stable cc wf jA cA vhv;
case _ Γ B V T A ptm ih =>
  have lem := compile_preserves_type_shape_arrow jA cA;
  cases lem; case _ A' lem =>
  cases lem; case _ B' lem =>
  cases lem; case _ jA' lem =>
  cases lem; case _ jB' lem =>
  cases lem; case _ e lem =>
  subst e
  cases lem; case _ cA' cB' =>
  have lem := compile_preserves_type_shape_arrow jR cR;
  cases lem; case _ A'' lem =>
  cases lem; case _ V' lem =>
  cases lem; case _ jA'' lem =>
  cases lem; case _ jV' lem =>
  cases lem; case _ e lem =>
  cases lem; subst e; case _ cA'' lem =>
  have u := types_have_unique_judgments h jA' jA''; cases u
  have cV := weaken_compile_type h jT cT (HsFrameWf.empty (hs_judgment_ctx_wf .type jA')) (hs_weaken_empty_type jT)
  have u := compile_type_uniqueness h jA' jA' cA' cA''; cases u;
  apply PrefixTypeMatch.arrow;
  apply @ih (.empty :: Γ') B' V' ([S]T') _ jB' cB' jV' lem (hs_weaken_empty_type jT) cV
  case _ => apply Judgment.wfempty wf

case _ Γ A B V T ptm ih =>
  have lem := compile_preserves_type_shape_all jA cA;
  cases lem; case _ A' lem =>
  cases lem; case _ B' lem =>
  cases lem; case _ cA' cB' =>
  have lem := compile_preserves_type_shape_all jR cR;
  cases lem; case _ A'' lem =>
  cases lem; case _ V' lem =>
  cases lem;
  cases jA; case _ jA1 jB =>
  cases jR; case _ jA2 jV =>

  have u := kinds_have_unique_judgments h jA1 jA2; cases u

  unfold compile_type at cA; simp at cA;
  rw[Option.bind_eq_some] at cA;
  cases cA; case _ A' cA =>
  cases cA; case _ cA cB =>
  rw[Option.bind_eq_some] at cB;
  cases cB; case _ B' cB =>
  cases cB; case _ cB e =>
  cases e
  unfold compile_type at cR; simp at cR;
  rw[Option.bind_eq_some] at cR;
  cases cR; case _ A'' cR =>
  cases cR; case _ cR cV =>
  rw[Option.bind_eq_some] at cV;
  cases cV; case _ V' cV =>
  cases cV; case _ cV e =>
  cases e
  have u := compile_kind_uniqueness h jA1 jA1 cA cR; cases u;
  have lem := compile_preserves_kinds wf jA1 cA;
  have wf' := hs_weaken_kind_type jA1 jT
  have cST := weaken_compile_type h jT cT (HsFrameWf.kind jA1) wf';
  apply PrefixTypeMatch.all;
  apply @ih (.kind A' :: Γ') B' V' ([S]T') _ jB cB jV cV wf' cST
  case _ => apply Judgment.wfkind lem wf
