import SystemFD.Ctx
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Metatheory.Classification

-- Surface syntax terms
inductive HsTerm : Type where
| HsVar : Nat -> HsTerm
| HsLam : Term -> HsTerm -> HsTerm
| HsApp : HsTerm -> HsTerm -> HsTerm
| HsLet : Term -> HsTerm -> HsTerm -> HsTerm
| HsIte : HsTerm -> HsTerm -> HsTerm -> HsTerm -> HsTerm
-- | HsType : Term -> HsTerm

protected def HsTerm.repr : (a : HsTerm) -> (p : Nat) -> Std.Format
| HsVar n , _ => "#" ++ Nat.repr n
| HsLam t1 t2 , p => "`λ" ++ Std.Format.sbracket (repr t1) ++ HsTerm.repr t2 p
| HsApp t1 t2, p => (HsTerm.repr t1 p) ++ " ⬝" ++ (HsTerm.repr t2 p)
| HsLet t1 t2 t3 , p => "let!" ++ HsTerm.repr t2 p ++ " : " ++ repr t1 ++";;" ++ Std.Format.line ++ HsTerm.repr t3 p
| HsIte t1 t2 t3 t4, p =>
  "if!" ++ HsTerm.repr t1 p ++ " ← " ++ HsTerm.repr t2 p ++
  "then" ++ Std.Format.line ++ HsTerm.repr t3 p ++
  "else" ++ Std.Format.line ++ HsTerm.repr t4 p
-- | HsType t , p => Term.repr t p

instance HsTerm_repr : Repr HsTerm where
  reprPrec a p := HsTerm.repr a p


namespace HsTerm
 @[simp]
 def size : HsTerm -> Nat
 | HsVar _ => 0
 | HsLam t1 t2 => Term.size t1 + size t2 + 1
 | HsApp t1 t2 => size t1 + size t2 + 1
 | HsLet t1 t2 t3 => Term.size t1 + size t2 + size t3 + 1
 | HsIte t1 t2 t3 t4 => size t1 + size t2 + size t3 + size t4 + 1
 -- | HsType t => Term.size t
end HsTerm

instance sizeOf_HsTerm : SizeOf HsTerm where
  sizeOf := HsTerm.size

inductive HsJudgment : Ctx Term -> HsTerm -> Term -> Prop where
| var :
  Judgment .wf Γ () ->
  (Γ d@ x).get_type = .some T ->
  HsJudgment Γ (.HsVar x) T
| lam :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (A -t> B, ★) ->
  HsJudgment (.type A :: Γ) t B ->
  HsJudgment Γ (.HsLam A t) (A -t> B)
| app :
  HsJudgment Γ t1 (A -t> B) ->
  HsJudgment Γ t2 A ->
  B' = B β[A] ->
  HsJudgment Γ (.HsApp t1 t2) B'
| letterm :
  HsJudgment Γ t1 A ->
  HsJudgment (.type A :: Γ) t2 ([S] B) ->
  HsJudgment Γ (.HsLet A t1 t2) B
-- TODO ite
-- | ite :
--   HsJudgment Γ t1 A ->
--   HsJudgment (.type A :: Γ) t2 ([S] B) ->
--   HsJudgment Γ (.HsLet A t1 t2) B


notation: 170 Γ:170 " ⊢s " t:170 " : " A:170 => HsJudgment Γ t A

inductive Compile : {Γ : Ctx Term} -> {t : HsTerm} -> {τ : Term} -> Γ ⊢s t : τ -> Term -> Prop where
| var :
  (j1 : Γ ⊢s (.HsVar i) : τ) ->
  Compile j1 (Term.var i)
| app :
  (j1 : Γ ⊢s t1 : (τ' -t> τ)) ->
  (j2 : Γ ⊢s t2 : τ') ->
  (j3 : Γ ⊢s (.HsApp t1 t2) : (τ β[t2'])) ->
  Compile j1 t1' ->
  Compile j2 t2' ->
  Compile j3 (t1' `@ t2')
| appev :
  (j1 : Γ ⊢s t1 : (π -t> τ)) -> -- Γ ⊢ t1 : F a => τ
  (ValidHeadVariable π Γ.is_opent) ->
  Γ ⊢ e : π ->
  Compile j1 t1' ->
  (j2 : Γ ⊢s t1 : (τ β[e])) ->
  Compile j2 (t1' `@ e)
| appt :
  (j1 : Γ ⊢s t1 : (∀[A]B)) -> -- Γ ⊢ t1 : ∀[A]τ
  Compile j1 t1' ->
  Γ ⊢ τ : A ->
  (j2 : Γ ⊢s t1 : (B β[τ])) ->
  Compile j2 (t1' `@t τ)
| lam :
  (j1 : (.type A :: Γ) ⊢s t1 : τ) ->
  (j2 : Γ ⊢s (.HsLam A t1) : (A -t> τ)) ->
  Compile j1 t1' ->
  Compile j2 (`λ[A] t1')
| letterm :
  Γ ⊢ A : ★ ->
  Γ ⊢ τ : ★ ->
  (j1 : Γ ⊢s t1 : A) ->
  Compile j1 t1' ->
  (j2 : (.term A t1' :: Γ) ⊢s t2 : ([S]τ)) ->
  Compile j2 t2' ->
  (j3 : Γ ⊢s (.HsLet A t1 t2) : τ) ->
  Compile j3 (.letterm A t1' t2')

notation:180 "⟅ " j:180 " ⟆=" t:180 => Compile j t

theorem compile_type_preserving :
  (j : Γ ⊢s t : τ) ->
  Compile j t' ->
  Γ ⊢ t' : τ := by
intro j1 j2;
induction j2;
case _ j1 =>
  cases j1; case _ h =>
  symm at h;
  apply Judgment.var; assumption; assumption;
case _ =>
  apply Judgment.app;
  assumption;
  assumption;
  rfl
case appev =>
  apply Judgment.app;
  assumption;
  assumption;
  rfl;
case appt =>
  apply Judgment.appt;
  assumption;
  assumption;
  rfl
case _ j2 _  j1  =>
  cases j2;
  apply Judgment.lam;
  assumption
  assumption
  assumption
case _ j1 c1 j2 c2 j3 ih1 ih2 =>
  apply Judgment.letterm
  assumption;
  assumption;
  assumption;
  assumption;
