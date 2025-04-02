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
  (j1 : Γ ⊢s A : `□) ->
  compile Γ A `□ j1 = .some A' ->
  CompileCtx (.kind A :: Γ) (.kind A' :: Γ')
| type :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢s A : `★) ->
  compile Γ A `★ j1 = .some A' ->
  CompileCtx (.type A :: Γ) (.type A' :: Γ')
| term :
  CompileCtx Γ Γ' ->
  (j1 : Γ ⊢s A : `★)  ->
  (j2 : Γ ⊢s t : τ) ->
  compile Γ A `★ j = .some A' ->
  compile Γ t τ j2 = .some t' ->
  CompileCtx (.term A t :: Γ) (.term A' t' :: Γ')


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
  Γ ⊢s τ : k ->
  Γ ⊢s τ : k' ->
  k = k' :=
 by
intro h j1 j2
induction τ generalizing Γ k k'
all_goals (cases h)
case _ => sorry
case _ ih1 ih2 kl1 kl2 =>
  have lem1 := @ih1 Γ `□ `□ kl1;
  sorry

theorem compile_preserves_kinds :
  HsKindLike t ->
  τ = `□ ->
  (j : Γ ⊢s t : τ) ->
  compile Γ t τ j = .some t' ->
  CompileCtx Γ Γ' ->
  Γ' ⊢ t' : .kind := by
 intro h e j c cc;
 induction Γ, t, τ, j using compile.induct generalizing t'
 all_goals try (cases e)
 all_goals try (cases h)
 case _ =>
   unfold compile at c; cases c;
   apply Judgment.ax;
   sorry
 case _ j1 j2 ih1 ih2 kl1 kl2 =>
   unfold compile at c; simp at c;
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
-- bogus cases
 case _ j1 ih1 =>  sorry
 case _ => sorry
 case _ => sorry
 case _ => sorry



def is_type : Ctx HsTerm -> HsTerm -> Option Unit
| Γ, .HsBind2 .arrow k k' => do
  let _ <- is_type Γ k
  let _ <- is_type (.empty :: Γ) k'
  .some ()
| Γ, .HsBind2 .farrow k k' => do
  let _ <- is_type Γ k
  let _ <- is_type (.empty :: Γ) k'
  .some ()
| Γ, `#x => if (Γ d@x).is_datatype then .some () else .none
| _, _ => .none
