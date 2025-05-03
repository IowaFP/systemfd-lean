import Hs.Algorithm
import Hs.Metatheory.Uniqueness
import Hs.Metatheory.Weaken
import Hs.Metatheory.WeakenCompile
import Hs.Metatheory.Substitution
import Hs.Metatheory.SubstitutionCompile
import Hs.Metatheory.TypeMatchCompile
import Hs.Metatheory.Preservation1

set_option maxHeartbeats 5000000

theorem compile_preserves_terms :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (∀ v, CompileCtxPred v) ->
  (∀ x,  (Γ d@ x).is_stable ->  (Γ' d@ x).is_stable) ->
  ⊢ Γ' ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  (j2 : Γ ⊢t t : τ) ->
  compile_term Γ t τ j2 = .some t' ->
  Γ' ⊢ t' : τ' := by
intro h cc cc' wf j1 c1 j2 c2;
induction Γ, t, τ, j2 using compile_term.induct generalizing Γ' t' τ' k
all_goals (unfold compile_term at c2; simp at c2)
case _ τ Γ x wf' test gt =>
     cases c2; simp at cc;
     have lem := @cc .type Γ Γ' x k τ τ' wf' (Eq.symm gt) j1 c1
     symm at lem;
     apply Judgment.var; assumption; assumption

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
 unfold compile_type at c1; cases j1; simp at c1;
 rw[Option.bind_eq_some] at c1;
 cases c1; case _ x1 c1' =>
 cases c1'; case _ c1' c2' =>
 rw[Option.bind_eq_some] at c2';
 cases c2'; case _ B' c2' =>
 cases c2'; case _ c2' e =>
 cases e; case _ ja jb =>
 have lem := compile_type_uniqueness h j1' ja c2 c1'; cases lem;
 have lem := compile_type_uniqueness h jb j3 c2' c3; cases lem;
 apply Judgment.lam;
 apply compile_preserves_types (cc .kind) wf h _ _ ja c1'
 case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type ja)
 case _ => unfold compile_kind; rfl
 case _ =>
   have j' := (hs_replace_empty_type ja jb)
   have lem := compile_replace_empty jb j' c2'
   apply @ih1 (.type A' :: Γ') `★ B' t' _ _ j' lem c4
   case _ => sorry
   apply Judgment.wftype
   apply compile_preserves_types (cc .kind) wf h _ _ j1' c2
   case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type j1')
   case _ => unfold compile_kind; rfl
   apply wf
 case _ =>
   apply Judgment.arrow;
   apply compile_preserves_types (cc .kind) wf h _ _ j1' c2
   case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type j1')
   case _ => unfold compile_kind; rfl
   have u := types_have_unique_judgments h j3 jb; cases u
   have lem1' := Judgment.wfempty wf
   have lem1 := HsJudgment.wfempty (hs_judgment_ctx_wf .type ja)
   have lem2 := HsJudgment.ax (hs_judgment_ctx_wf .type ja)
   apply compile_preserves_types (cc .kind) _ h _ _ j3 c3
   case _ => apply lem1'
   case _ => have lem := hs_weaken_empty_kind lem2; simp at lem; apply lem
   case _ =>
     unfold hs_weaken_empty_kind; unfold hs_weaken_kind; cases lem2;
     unfold hs_judgment_ctx_wf; simp;
     unfold hs_rename; simp; unfold compile_kind; rfl

case _ Γ t1 A B t2 h1 h2 h3 h4 ih1 ih2 => -- app
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ AB' c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ A' c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ wB' c4 =>
 cases c4; case _ c4 c5 =>
 rw[Option.bind_eq_some] at c5;
 cases c5; case _ t1' c5 =>
 cases c5; case _ c5 c6 =>
 rw[Option.bind_eq_some] at c6;
 cases c6; case _ t2' c6 =>
 cases c6; case _ c6 e =>
 cases e;
 have u := types_have_unique_kinds j1 h4; cases u;
 have lem := compile_preserves_type_shape_arrow (extract_typing h1) c2
 cases lem; case _ wA lem =>
 cases lem; case _ wB lem  =>
 cases lem; case _ ja' lem =>
 cases lem; case _ jb' lem =>
 cases lem; case _ e lem =>
 cases lem; case _ c1' c2' =>
   cases e;
   have lem := compile_type_uniqueness h h3 ja' c3 c1'; cases lem
   have lem := compile_beta_empty_term jb' c2' h2 c6 (hs_beta_empty_type t2 jb');
   have lem' := compile_type_uniqueness h (hs_beta_empty_type t2 jb') j1 lem c1
   apply Judgment.app;
   case _ =>
     have ih' := @ih1 Γ' `★ (A' -t> wB) t1' cc' wf (extract_typing h1) c2 c5;
     apply ih'
   case _ =>
     have ih' :=  @ih2 Γ' `★ A' t2' cc' wf h3 c3 c6
     apply ih'
   symm at lem'; apply lem'

case _ B Γ A t1 t2 j1' j2 j3 j4 ih1 ih2 => -- letterm
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ A' c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ t1' c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ t2' c4 =>
 cases c4; case _ c4 e =>
 cases e;
 have lemA : Γ' ⊢ A' : ★ := by
   apply compile_preserves_types (cc .kind) wf h _ _ j1' c2;
   apply HsJudgment.ax (hs_judgment_ctx_wf .type j1')
   unfold compile_kind; rfl
 have lemt1 := @ih1 Γ' `★ A' t1' cc' wf j1' c2 c3
 have lem := types_have_unique_kinds j1 j3; cases lem;
 have lemΓ' := by apply Judgment.wfterm; assumption; assumption; assumption
 have lemΓ : ⊢s (.term A t1 :: Γ) := by apply HsJudgment.wfterm; assumption; assumption; (apply hs_judgment_ctx_wf .type j1')
 apply Judgment.letterm;
 case _ => assumption
 case _ => assumption
 case _ =>
   apply @ih2 (.term A' t1' :: Γ') `★ ([S]τ') t2' _ _ _ _ c4;
   case _ => sorry
   case _ => assumption
   case _ => apply hs_weaken_type lemΓ j1
   case _ => apply weaken_compile_type h j1 c1 (HsFrameWf.term j1' j2)
 case _ =>
   apply compile_preserves_types (cc .kind) wf h _ _ _ c1;
   apply HsJudgment.ax (hs_judgment_ctx_wf .type j1)
   unfold compile_kind; rfl
case _ T Γ A R B p s i t jA jR jB jT jp js ji jt j9 j10 j11 j12 ih1 ih2 ih3 ih4 =>
 have u := types_have_unique_kinds jT j1; cases u;
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ wA c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ wR c3 =>
 cases c3; case _ c3 c4 =>
 rw[Option.bind_eq_some] at c4;
 cases c4; case _ wB c4 =>
 cases c4; case _ c4 c5 =>
 rw[Option.bind_eq_some] at c5;
 cases c5; case _ wT c5 =>
 cases c5; case _ c5 c6 =>
 rw[Option.bind_eq_some] at c6;
 cases c6; case _ wp c6 =>
 cases c6; case _ c6 c7 =>
 rw[Option.bind_eq_some] at c7;
 cases c7; case _ ws c7 =>
 cases c7; case _ c7 c8 =>
 rw[Option.bind_eq_some] at c8;
 cases c8; case _ wi c8 =>
 cases c8; case _ c8 c9 =>
 rw[Option.bind_eq_some] at c9;
 cases c9; case _ wt c9 =>
 cases c9; case _ c9 e =>
 cases e;
 have lemAx : Γ ⊢κ `★ : `□ := by apply HsJudgment.ax (hs_judgment_ctx_wf .type jA)
 have lemK : compile_kind Γ `★ `□ lemAx = .some ★ := by unfold compile_kind; cases lemAx; simp
 apply Judgment.ite;
 apply @ih1 Γ' `★ wA wp cc' wf jA c2 c6;
 apply @ih2 Γ' `★ wR ws cc' wf jR c3 c7
 apply compile_preserves_types (cc .kind) wf h lemAx lemK jR c3
 apply @ih3 Γ' `★ wB wi cc' wf jB c4 c8;
 apply compile_preserves_vhv_terms Γ.is_ctor Γ'.is_ctor cc wf jp c6 j12
 apply compile_preserves_vhv_types Γ.is_datatype Γ'.is_datatype cc wf jR c3 j11
 apply compile_stable_match h cc' wf jA c2 jR c3 j9
 apply compile_prefix_match h cc' wf jA c2 jB c4 j1 c1 j10
 apply compile_preserves_types (cc .kind) wf h lemAx lemK j1 c1
 apply @ih4 Γ' `★ τ' wt cc' wf j1 c1
 apply c9

-- implicits
case _ Γ A t τ e h1 h2 h3 h4 ih => -- implicitAllE
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
   have ih' := @ih Γ' `★ (∀[A']τ') wt cc' wf h1 c2 c4;
   apply ih'
 case _ =>
   have h' := compile_preserves_types (cc .kind) wf h h2 c3 h4 c5
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
   have h' := compile_preserves_types (cc .kind) wf h h2 c3 h4 c5
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

case _ Γ t A τ j1' j2 ih =>
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
  have lem : ⊢ (.kind wA :: Γ') := by
    apply Judgment.wfkind;
    apply compile_preserves_kinds wf j2 c1; assumption
  apply Judgment.lamt;
  apply compile_preserves_kinds wf j2 c1
  apply @ih (Frame.kind wA :: Γ') `★ wt' wt _ lem j1 c2' c2;
  case _ => sorry
  case _ =>
    apply Judgment.allt;
    apply compile_preserves_kinds wf j2 c1;
    apply compile_preserves_types (cc .kind) lem h _ _ j1 c2'
    case _ =>
      apply HsJudgment.ax;
      apply HsJudgment.wfkind; assumption
      apply (hs_judgment_ctx_wf .kind j2)
    case _ =>
      unfold compile_kind; rfl;

case _ Γ t π τ j1' j2 j4 j3 ih1 => -- implicitArrI
 rw[Option.bind_eq_some] at c2;
 cases c2; case _ π' c2 =>
 cases c2; case _ c2 c3 =>
 rw[Option.bind_eq_some] at c3;
 cases c3; case _ t' c3 =>
 cases c3; case _ c3 e =>
 cases e;
 unfold compile_type at c1; cases j1; simp at c1;
 rw[Option.bind_eq_some] at c1;
 cases c1; case _ x1 c1' =>
 cases c1'; case _ c1' c2' =>
 rw[Option.bind_eq_some] at c2';
 cases c2'; case _ B' c2' =>
 cases c2'; case _ c2' e =>
 cases e; case _ ja _ jb =>
 have lem := compile_type_uniqueness h j1' ja c2 c1'; cases lem;
 apply Judgment.lam;
 apply compile_preserves_types (cc .kind) wf h _ _ ja c1'
 case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type ja)
 case _ => unfold compile_kind; rfl
 case _ =>
   have j' := (hs_replace_empty_type ja jb)
   have lem := compile_replace_empty jb j' c2'
   apply @ih1 (.type π' :: Γ') `★ B' t' _ _ j' lem c3
   case _ => sorry
   apply Judgment.wftype
   apply compile_preserves_types (cc .kind) wf h _ _ j1' c2
   case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type j1')
   case _ => unfold compile_kind; rfl
   apply wf
 case _ =>
   apply Judgment.arrow;
   apply compile_preserves_types (cc .kind) wf h _ _ j1' c2
   case _ => apply HsJudgment.ax (hs_judgment_ctx_wf .type j1')
   case _ => unfold compile_kind; rfl
   have lem1' := Judgment.wfempty wf
   have lem1 := HsJudgment.wfempty (hs_judgment_ctx_wf .type ja)
   have lem2 := HsJudgment.ax (hs_judgment_ctx_wf .type ja)
   apply compile_preserves_types (cc .kind) _ h _ _ jb c2';
   case _ => apply lem1'
   case _ => have lem := hs_weaken_empty_kind lem2; simp at lem; apply lem
   case _ =>
     unfold hs_weaken_empty_kind; unfold hs_weaken_kind; cases lem2;
     unfold hs_judgment_ctx_wf; simp;
     unfold hs_rename; simp; unfold compile_kind; rfl
case _ Γ t π τ e j1' j2 j3 ih1 ih2 => -- implicitArrE
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ warr c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ wπ c3 =>
  cases c3; case _ c3 c4 =>
  rw[Option.bind_eq_some] at c4;
  cases c4; case _ wt c4 =>
  cases c4; case _ c4 c5 =>
  rw[Option.bind_eq_some] at c5;
  cases c5; case _ we c5 =>
  cases c5; case _ c5 e =>
  cases e;
  have u := types_have_unique_kinds j3 j1; cases u
  have lem := compile_preserves_type_shape_farrow (extract_typing j1') c2;
  cases lem; case _ wA lem =>
  cases lem; case _ wB lem  =>
  cases lem; case _ ja' lem =>
  cases lem; case _ jb' lem =>
  cases lem; case _ e lem =>
  cases lem; case _ c1' c2' =>
  cases e;
  have lem := compile_beta_empty_term jb' c2' j2 c5 j1;
  apply Judgment.app;
  case _ =>
    apply @ih1 Γ' `★ (wA -t> wB) wt cc' wf (extract_typing j1') c2 c4
  case _ => apply @ih2 Γ' `★ wA we cc' wf ja' c1' c5
  case _ =>
    have e' : compile_type Γ ([Subst.Action.su e::I]τ) ([Subst.Action.su e::I]`★) j1 =
              compile_type Γ ([Subst.Action.su e::I]τ) `★ j1 := by rfl
    rw[e'] at lem; rw[c1] at lem; injection lem
