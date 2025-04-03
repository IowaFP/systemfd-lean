import Hs.Algorithm

inductive HsKindLike : HsTerm -> Prop where
| HsType : HsKindLike `★
| HsArrK : HsKindLike k -> HsKindLike k' -> HsKindLike (k `-k> k')

inductive CompileCtx : Ctx HsTerm -> Ctx Term -> Prop where
| nil : CompileCtx [] []
| empty :
  CompileCtx Γ Γ' ->
  CompileCtx (.empty :: Γ) (.empty :: Γ')
| kind :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢κ A : `□) ->
  compile_kind Γ A `□ j1 = .some A' ->
  CompileCtx (.kind A :: Γ) (.kind A' :: Γ')
| type :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★) ->
  compile_type Γ A `★ j1 = .some A' ->
  CompileCtx (.type A :: Γ) (.type A' :: Γ')
| term :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢τ A : `★)  ->
  (j2 : Γ ⊢t t : τ) ->
  compile_type Γ A `★ j = .some A' ->
  compile_term Γ t τ j2 = .some t' ->
  CompileCtx (.term A t :: Γ) (.term A' t' :: Γ')

theorem compile_preserves_indices :
  CompileCtx Γ Γ' ->
  (j2 : Γ ⊢κ  T : `□) ->
  (j1 : Γ ⊢τ `#x : T) ->
  compile_kind Γ T `□ j = .some T' ->
  (Γ' d@ x).get_type = .some T' := by
intro cc j1 j2 ct;
cases j2;
induction cc;
case _ wf h gt => unfold Frame.get_type at gt; simp at gt;
case _ wf h gt => sorry
case _ => sorry
case _ => sorry
case _ => sorry



theorem compile_ctx_wf :
  ⊢s Γ ->
  CompileCtx Γ Γ' ->
  ⊢ Γ' := by
intro h1 h2;
induction h2;
case _ => apply Judgment.wfnil
case _ h1 ih1 =>
  cases h1; case _ h1 =>
  apply Judgment.wfempty;
  apply ih1 h1;
case _ h1 j1 cc ih =>
 apply Judgment.wfkind;
 sorry
 sorry
case _ => sorry
case _ => sorry

theorem kinding_uniqueness :
  HsKindLike τ ->
  Γ ⊢κ τ : k ->
  Γ ⊢κ τ : k' ->
  k = k' :=
 by
intro h j1 j2
induction τ generalizing Γ k k'
all_goals (cases h)
case _ => cases j1; cases j2; rfl
case _ ih1 ih2 kl1 kl2 =>
  cases j1; cases j2; rfl;

theorem compile_preserves_kinds :
  HsKindLike t ->
  τ = `□ ->
  (j : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j = .some t' ->
  CompileCtx Γ Γ' ->
  Γ' ⊢ t' : .kind := by
 intro h e j c cc;
 induction Γ, t, τ, j using compile_kind.induct generalizing t'
 all_goals try (cases e)
 all_goals try (cases h)
 case _ =>
   unfold compile_kind at c; cases c;
   case _ wf =>
     apply Judgment.ax;
     apply compile_ctx_wf wf cc
 case _ j1 j2 ih1 ih2 kl1 kl2 =>
   unfold compile_kind at c; simp at c;
   rw[Option.bind_eq_some] at c;
   cases c; case _ w1 c1 =>
   cases c1; case _ c1 c2 =>
   rw[Option.bind_eq_some] at c2;
   cases c2; case _ w2 c2 =>
   cases c2; case _ c2 c3 =>
   cases c3;
   have ih1' := @ih1 w1 kl1 rfl c1 cc;
   have ih2' := @ih2 w2 kl2 rfl c2 cc;
   apply Judgment.allk;
   apply ih1';
   apply ih2'

inductive HsTypeLike : Ctx HsTerm -> HsTerm -> Prop where
| HsArr : HsTypeLike Γ τ -> HsTypeLike (.empty::Γ) τ' -> HsTypeLike Γ (τ → τ')
| HsFArr : HsTypeLike Γ τ -> HsTypeLike (.empty::Γ) τ' -> HsTypeLike Γ (τ ⇒ τ')
| HsVarTy : (Γ d@x).is_datatype || (Γ d@ x).is_kind -> HsTypeLike Γ (`#x)
| HsAll : HsKindLike A -> HsTypeLike (.kind A::Γ) τ -> HsTypeLike Γ (`∀{A} τ)

theorem typing_uniqueness :
  HsTypeLike Γ t ->
  Γ ⊢τ t : k ->
  Γ ⊢τ t : k' ->
  k = k' := by
intro h j1 j2;
induction t generalizing Γ;
all_goals (cases h)
case _ =>
  cases j1; cases j2
  case _ h2 _ _ h1 =>
  rw [<-h1] at h2; injection h2;
case _ =>
  cases j1; cases j2;
  case _ tl1 _ j1 _ _ j2 _ _ ih1 _ =>
  apply ih1 tl1 j1 j2
case _ =>
  cases j1; cases j2;
  case _ tl1 _ j1 _ _ j2 _ _ ih1 _ =>
  apply ih1 tl1 j1 j2
case _ =>
  cases j1; cases j2;
  case _ j2 _ _ _ j1 _ ih =>
  apply ih j2 j1 j1

theorem compile_preserves_types :
  HsKindLike k ->
  (j2 : Γ ⊢κ k : `□) ->
  compile_kind Γ k `□ j2 = .some k' ->
  HsTypeLike Γ τ ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  CompileCtx Γ Γ' ->
  Γ' ⊢ τ' : k' := by
intro kl j1 c1 tl j2 c2 cc;
induction Γ, τ, k, j2 using compile_type.induct generalizing Γ' τ' k'
all_goals (unfold compile_type at c2; simp at c2)
case _ =>
  cases c2;
  apply Judgment.var;
  apply compile_ctx_wf; assumption; assumption;
  sorry
case _ h1 h2 ih1 ih2 => cases tl
case _ h1 h2 ih1 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e; unfold compile_kind at c1; cases j1;
  simp at c1; cases c1;
  cases tl; case _ kl1 kl2 =>
  apply Judgment.allt;
  apply compile_preserves_kinds kl1 rfl h1 c2 cc;
  apply @ih1 ★ w2 (.kind w1 :: Γ') .HsType _ _ kl2 c3 _
  case _ => apply HsJudgment.ax; apply HsJudgment.wfkind; assumption; assumption
  case _ => unfold compile_kind; rfl
  case _ => apply CompileCtx.kind; assumption; assumption
case _ j1 _ j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e; cases tl;
  have lem1 := compile_preserves_kinds kl rfl j1 c1 cc;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  case _ tl1 tl2 _ =>
  apply Judgment.arrow;
  apply @ih1 ★ w1 Γ' .HsType _ _ tl1 c2 cc;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 ★ w2 (.empty::Γ') .HsType _ _ tl2 c3 _
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl
  case _ => apply CompileCtx.empty; assumption
case _ j1 _ j2 ih1 ih2 =>
  rw[Option.bind_eq_some] at c2;
  cases c2; case _ w1 c2 =>
  cases c2; case _ c2 c3 =>
  rw[Option.bind_eq_some] at c3;
  cases c3; case _ w2 c3 =>
  cases c3; case _ c3 e =>
  cases e; cases tl;
  have lem1 := compile_preserves_kinds kl rfl j1 c1 cc;
  unfold compile_kind at c1; simp at c1;
  cases j1; simp at c1; cases c1;
  case _ tl1 tl2 _ =>
  apply Judgment.arrow;
  apply @ih1 ★ w1 Γ' .HsType _ _ tl1 c2 cc;
  case _ => apply HsJudgment.ax; assumption
  case _ => unfold compile_kind; rfl
  apply @ih2 ★ w2 (.empty::Γ') .HsType _ _ tl2 c3 _
  case _ => apply HsJudgment.ax; apply HsJudgment.wfempty; assumption
  case _ => unfold compile_kind; rfl
  case _ => apply CompileCtx.empty; assumption

inductive HsTermLike : Ctx HsTerm -> HsTerm -> Prop where
| HsVar : (Γ d@ x).is_ctor || (Γ d@ x).is_type -> HsTermLike Γ `#x
| HsApp : HsTermLike Γ t1 -> HsTermLike Γ t2 -> HsTermLike Γ (t1 `• t2)
| HsLam : HsTermLike (.type A :: Γ) t1 -> HsTermLike Γ (`λ{A}t1)
| HsIte : HsTermLike Γ p -> HsTermLike Γ i -> HsTermLike Γ t -> HsTermLike Γ e -> HsTermLike Γ (.HsIte p i t e)
| HsLet : HsTypeLike Γ A -> HsTermLike Γ t -> HsTermLike (.term A t :: Γ) t' -> HsTermLike Γ (.HsLet A t t')


theorem compile_preserves_typing :
  CompileCtx Γ Γ' ->
  HsTypeLike Γ τ ->
  (j1 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some τ' ->
  HsTermLike Γ t ->
  (j2 : Γ ⊢t t : τ) ->
  compile_term Γ t τ j2 = .some t' ->
  Γ' ⊢ t' : τ' := by
intro cc τl j1 c1 tl j2 c2;
induction Γ, t, τ, j2 using compile_term.induct generalizing Γ' t' τ' k
cases tl;
all_goals (unfold compile_term at c2; simp at c2)
case _ => cases c2; sorry
case _ =>
 sorry
case _ =>
 sorry
case _ =>
 sorry
case _ =>
 sorry

-- implicits
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
