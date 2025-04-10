import Hs.CompileJ
import Hs.Metatheory.Weaken

inductive HsKindCompile : HsTerm -> Term -> Prop
| HsType : HsKindCompile `★ ★
| HsArrk : HsKindCompile k1 k1' -> HsKindCompile k2 k2' -> HsKindCompile (k1 `-k> k2) (k1' -k> k2')

@[simp]
abbrev CompilePreservesKinds : (v : HsVariant) -> (Γ : Ctx HsTerm) -> (CompileJArgs v Γ) -> Prop
| .kind => λ Γ => λ ⟨k, ki ; j , k'⟩ =>
  CompileJ .kind Γ ⟨k, ki; j, k'⟩ ->
  HsKindCompile k k'
| _ => λ _ => λ _ => true

theorem compile_preserves_kinds_lemma :
  CompileJ v Γ idx ->
  CompilePreservesKinds v Γ idx := by
intro j; induction j <;> simp at *;
case _ =>
 intro j; apply HsKindCompile.HsType;
case _ h1 h2 ih1 ih2=>
  intro j;
  apply HsKindCompile.HsArrk;
  apply ih1 h1;
  apply ih2 h2;

theorem compile_preserves_kind_shape :
  (j : Γ ⊢κ k : `□) ->
  CompileJ .kind Γ ⟨k, `□; j, k'⟩ ->
  HsKindCompile k k' := by
intro j cj;
have lem := compile_preserves_kinds_lemma cj; simp at lem;
apply lem cj;

inductive HsTypeCompile : Ctx HsTerm -> HsTerm -> Term -> Prop
| HsVar :
  (Γ d@ x).is_datatype ->
  HsTypeCompile Γ (`#x) (#x)
| HsArrow :
  HsTypeCompile Γ t1 t1' ->
  HsTypeCompile (.empty :: Γ) t2 t2' ->
  HsTypeCompile Γ (t1 → t2) (t1' -t> t2')
| HsFArrow :
  HsTypeCompile Γ t1 t1' ->
  HsTypeCompile (.empty :: Γ) t2 t2' ->
  HsTypeCompile Γ (t1 ⇒ t2) (t1' -t> t2')
| HsAll :
  HsTypeCompile (.kind A :: Γ) t t' ->
  HsKindCompile A A' ->
  HsTypeCompile Γ (`∀{A} t) (∀[A']t')
| HsAppk :
  HsTypeCompile Γ t1 t1' ->
  HsTypeCompile Γ t2 t2' ->
  HsTypeCompile Γ (t1 `•k t2) (t1' `@k t2')

theorem weaken_term_hs_type_compile :
  HsTypeCompile Γ τ τ' ->
  Γ ⊢τ A : `★ ->
  Γ ⊢t t : A ->
  HsTypeCompile (.term A t :: Γ) ([S]τ) ([S]τ') := by
intro j1 j2 j3;
 sorry

theorem hs_type_compile_unique :
  HsTypeCompile Γ τ τ' -> HsTypeCompile Γ τ τ'' -> τ' = τ'' := by
intro j1 j2;
induction j2;
case _ => sorry
case _  =>
  sorry
case _ => sorry
case _ => sorry
case _ => sorry

@[simp]
abbrev  CompilePreservesTypes : (v : HsVariant) -> (Γ : Ctx HsTerm) -> CompileJArgs v Γ -> Prop
| .type => λ Γ => λ ⟨τ, k; j, τ'⟩ =>
  CompileJ .type Γ ⟨τ, k; j, τ'⟩ ->
  HsTypeCompile Γ τ τ'
| _ => λ _ => λ _ => true

theorem compile_preserves_type_shape_lemma :
  CompileJ v Γ idx ->
  CompilePreservesTypes v Γ idx := by
intro j; induction j <;> simp at *;
case _ h1 h2 ih1 ih2 _ _ =>
  intro j;
  apply HsTypeCompile.HsAppk;
  apply ih1 h1
  apply ih2 h2
case _ h1 h2 ih1 ih2 =>
  intro j;
  apply HsTypeCompile.HsArrow;
  apply ih1 h1
  apply ih2 h2
case _ h1 h2 ih1 ih2 =>
  intro j;
  apply HsTypeCompile.HsFArrow;
  apply ih1 h1
  apply ih2 h2

theorem compile_preserves_type_shape :
  (j : Γ ⊢τ τ : k) ->
  CompileJ .type Γ ⟨τ, k; j, τ'⟩ ->
  HsTypeCompile Γ τ τ' := by
intro j1 j2;
have lem := compile_preserves_type_shape_lemma j2; simp at lem;
apply lem j2;

theorem compile_type_uniqueness :
  (j : Γ ⊢τ A : `★) ->
  CompileJ .type Γ ⟨A, `★; j, A'⟩ ->
  CompileJ .type Γ ⟨A, `★; j, A''⟩ ->
  A' = A''
:= by
intro j1 c1 c2;
have lem1 := compile_preserves_type_shape j1 c1;
have lem2 := compile_preserves_type_shape j1 c2;
apply hs_type_compile_unique lem1 lem2;


theorem compile_preserves_indices :
  CompileJ .ctx Γ Γ' ->
  (Γ d@ x).get_type = .some τ ->
  CompileJ .type Γ ⟨τ, `★; j, τ'⟩ ->
  (Γ' d@ x).get_type = .some τ' := by
intro cc gt cτ;
cases cc;
case _ => cases gt
case _ =>
  simp at j;
  induction x;
  case _ => cases gt
  case _ n ih =>
  simp at gt;
  cases gt; case _ w gt =>
  cases gt; case _ gt e =>
  subst e;
  sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry

theorem compile_preserves_validctors :
  (j : Γ ⊢τ τ : `★) ->
  ValidHsCtorType Γ τ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .type Γ ⟨τ, `★; j, τ'⟩ ->
  ValidCtorType Γ' τ' := by
intros j1 j2 j3 j4;
induction j2;
case _ v =>
  apply ValidCtorType.refl;
  unfold HsValidHeadVariable at v;
  unfold ValidHeadVariable; sorry
case _ => sorry
case _ => sorry
case _ => sorry


-- needs some sort of classification lemma?
@[simp]
abbrev CompileCtxWfType : (v : HsVariant) -> (Γ : Ctx HsTerm) -> (CompileJArgs v Γ) -> Prop
| .term => λ Γ => λ ⟨t , τ; j , t'⟩ => ∀ Γ' τ',
  CompileJ .ctx Γ Γ' ->
  HsTypeCompile Γ τ τ' ->
  CompileJ .term Γ ⟨t, τ; j, t'⟩ ->
  (jk : Γ ⊢τ τ : `★) ->
  CompileJ .type Γ ⟨τ, `★; jk, τ'⟩ ->
  (Γ' ⊢ t' : τ')
| .type => λ Γ => λ ⟨τ , k; j , τ'⟩ => ∀ Γ' k',
  CompileJ .ctx Γ Γ' ->
  HsKindCompile k k' ->
  (jk : Γ ⊢κ k : `□) ->
  CompileJ .kind Γ ⟨k, `□; jk, k'⟩ ->
  CompileJ .type Γ ⟨τ, k; j, τ'⟩ ->
  (Γ' ⊢ τ' : k')
| .kind => λ Γ => λ ⟨k, ki ; j , k'⟩ => ∀ Γ',
  ki = `□ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .kind Γ ⟨k, ki; j, k'⟩ ->
  (Γ' ⊢ k' : □)
| .ctx => λ Γ => λ Γ' => ⊢s Γ -> CompileJ .ctx Γ Γ' -> ⊢ Γ'

theorem compile_preserves_typing :
 CompileJ v Γ idx -> CompileCtxWfType v Γ idx :=
by
intro j; induction j <;> simp at *;
case _ => intro wf cc; apply Judgment.wfnil
case _ ih =>
  intro wf cc
  cases cc; cases wf;
  case _ cc wf =>
  apply Judgment.wfempty (ih wf cc);
case _  Γ' j c1 c2 ih1 ih2 =>
  intro wf cc
  cases cc; cases wf;
  case _ cc wf _ =>
  apply Judgment.wftype;
  have ih1' := ih1 Γ' ★ c2; simp at ih1';
  have ih1'' := ih1' .HsType (HsJudgment.ax wf) (CompileJ.type _) c1;
  assumption
  apply ih2 wf c2;
case _ Γ' j1 c1 c2 ih1 ih2 =>
  intro wf cc
  cases cc; cases wf;
  case _ c3 cc wf _ =>
  apply Judgment.wfkind;
  apply ih2 Γ' c2 c1
  apply ih1 wf c2
case _ Γ' j1 c1 c2 ih1 ih2 =>
  intro wf cc
  cases cc; cases wf;
  case _ cc wf _ =>
  apply Judgment.wfdatatype
  apply ih2 Γ' c2 c1
  apply ih1 wf c2
case _ Γ' j1 c1 c2 ih1 ih2 =>
  intro wf cc
  cases cc; cases wf;
  case _ cc wf _ j4 =>
  apply Judgment.wfctor;
  have ih1' := ih1 Γ' ★; simp at ih1';
  have ih1'' := ih1' cc .HsType (HsJudgment.ax wf) (CompileJ.type _) c1;
  assumption;
  apply ih2 wf c2
  apply compile_preserves_validctors j1 j4 c2 c1;
case _ Γ _ _  A' _ Γ' j1 j2 c1 c2 c3 ih1 ih2 ih3 =>
  intro wf cc
  cases cc; cases wf;
  case _ j1' j2' c1' c2' cc wf _ _ =>
  apply Judgment.wfterm;
  have ih1' := ih1 Γ' ★; simp at ih1';
  have ih1'' := ih1' cc .HsType (HsJudgment.ax wf) (CompileJ.type _) c1; assumption
  have ih2' := ih2 Γ' A' c3 (compile_preserves_type_shape j1' c1') c2 j1 c1; assumption;
  apply ih3 wf c3
case type j =>
  intro Γ' cc cc'
  cases cc';
  apply Judgment.ax;
  have wf := hs_judgment_ctx_wf .kind j
  sorry

case arrowk j1 j2 j3 c1 c2 ih1 ih2 =>
  intro Γ' cc cc';
  apply Judgment.allk
  apply ih1 Γ' cc c1
  apply ih2 Γ' cc c2

case appk Γ _ κ1 κ2 _ κ1' κ2' jk2 _ _ _ _ j1 jk1 ck1 ck2 c1 c2 ihk1 ihk2 ih1 ih2 =>
  simp at jk2;
  intro Γ' k' cc h1 h2 jk2' cc'; -- k' = κ2'
  cases ck1; case _ j1' j2' jk1'' jk2'' =>
  replace ihk2 := ihk2 Γ' κ1' cc (compile_preserves_kind_shape j1' jk1'') j1' jk1'' c2;
  have lem1 : CompileJ .kind Γ ⟨(κ1 `-k> κ2), `□; jk1, (κ1' -k> k')⟩ := by
    apply CompileJ.arrowk; apply jk1''; apply jk2'
  have lem2 : HsKindCompile (κ1 `-k> κ2) (κ1' -k> k') := by
    apply HsKindCompile.HsArrk;
    apply compile_preserves_kind_shape j1' jk1''
    apply h1
  have ihk1'  := ihk1 Γ' (κ1' -k> k') cc lem2 jk1 lem1 c1;
  apply Judgment.appk;
  apply ihk1';
  apply ihk2;

case arrow j1 j2 j3 h1 h2 ih1 ih2 =>
  intro Γ' k' cc kl; cases kl;
  intro jk ck ct;
  apply Judgment.arrow;
  apply ih1 Γ' ★ cc .HsType jk ck h1;
  have wax := hs_weaken_empty_kind jk; simp at wax;
  apply ih2 (.empty :: Γ') ★ (.wfempty cc) .HsType wax _ h2
  case _ => apply CompileJ.type;

case farrow j1 j2 j3 h1 h2 ih1 ih2 =>
  intro Γ' k' cc kl; cases kl;
  intro jk ck ct;
  apply Judgment.arrow;
  apply ih1 Γ' ★ cc .HsType jk ck h1;
  have wax := hs_weaken_empty_kind jk; simp at wax;
  apply ih2 (.empty :: Γ') ★ (.wfempty cc) .HsType wax _ h2
  case _ => apply CompileJ.type;

case appev Γ π τ e t1 π' τ' e' t1' τ'' j1 j2 j3 j4 _ c1 c2 c3 c4 eq c5 ih1 ih2 ih3 ih4 =>
  intro Γ' cτ'' cc tl ct jk cτ
  have ih1' := ih1 Γ'
  apply Judgment.app;
  sorry -- apply ih2 Γ' (π' ⇒ τ')
  sorry
  sorry
  sorry
  sorry

case appt => sorry

case lamt => sorry

case lamev => sorry

case var Γ x τ wf gt j1 =>
  intro Γ' τ' cc tl cc' jτ cτ
  have lem := compile_preserves_indices cc gt cτ;
  apply Judgment.var sorry (Eq.symm lem);

case app j1 j2 j3 c1 c2 ih1 ih2 => sorry

case lam Γ A t1 τ A' t1' j1 j2 j3 c1 c2 ih1 ih2 =>
  intro Γ' τ' cc tl cc' jτ cτ;
  cases tl; case _ τ1' τ2' tl1 tl2 =>
  cases cτ; case _  j1' j1' j2' c2' =>
  have lem1 := compile_preserves_type_shape j1 c1;
  have e := hs_type_compile_unique tl1 lem1; symm at e; subst e;
  have lem2 := compile_preserves_type_shape j1' c2';
  apply Judgment.lam;
  apply ih1 Γ' ★ cc .HsType (HsJudgment.ax (hs_judgment_ctx_wf .type j1)) (CompileJ.type _) c1;
  have ih2' := ih2 (.empty ::Γ') τ2' sorry
  sorry
  sorry

  -- cases c1'; case _ τ1' τ2' tl1 tl2 =>
  -- have ih1' := ih1 Γ' ★ cc .HsType (HsJudgment.ax (hs_judgment_ctx_wf .prf j1)) sorry c1;
  -- have ih2' := ih2 (.type A' :: Γ') τ2' sorry sorry c2
  -- have lem := @Judgment.lam Γ' A' t1' τ2' ih1' sorry sorry;
  -- sorry

case _ Γ A τ t1 t2 A' τ' t1' t2' j1 j2 j3 j4 j5 c1 c2 c3 c4 ih1 ih2 ih3 ih4 =>
  intro Γ' τ'' cc tl cc' j1' c1'
  apply Judgment.letterm
  apply ih1 Γ' ★ cc .HsType (HsJudgment.ax (hs_judgment_ctx_wf .type j1)) (CompileJ.type _) c1
  clear ih1;
  apply ih3 Γ' A' cc (compile_preserves_type_shape j1 c1) c3 j1 c1
  clear ih3;
  have lem1 := CompileJ.wfterm j1 j3 c1 c3 cc;
  have lem2 := weaken_term_hs_type_compile tl j1 j3
  have lem3 := hs_weaken_term_type j1 j3 j2;
  apply ih4 (.term A' t1':: Γ') ([S]τ'') _ _ c4 lem3 _
  case _ => apply lem1
  case _ => apply lem2
  case _ => sorry
  sorry -- apply ih2 Γ' ★ cc sorry c2 j1 c1;

case _ =>
  intro Γ' τ' cc tl c5 j1 c1
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
