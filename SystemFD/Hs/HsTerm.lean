import SystemFD.Ctx
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Metatheory.Classification

set_option maxHeartbeats 500000

-- Surface syntax terms
inductive HsTerm : Type where
| HsVar : Nat -> HsTerm
| HsLam : Term -> HsTerm -> HsTerm
| HsApp : HsTerm -> HsTerm -> HsTerm
| HsLet : Term -> HsTerm -> HsTerm -> HsTerm
| HsIte : Nat -> HsTerm -> HsTerm -> HsTerm -> HsTerm
-- | HsType : Term -> HsTerm

protected def HsTerm.repr : (a : HsTerm) -> (p : Nat) -> Std.Format
| HsVar n , _ => "#" ++ Nat.repr n
| HsLam t1 t2 , p => "`λ" ++ Std.Format.sbracket (repr t1) ++ HsTerm.repr t2 p
| HsApp t1 t2, p => (HsTerm.repr t1 p) ++ " ⬝" ++ (HsTerm.repr t2 p)
| HsLet t1 t2 t3 , p => "let!" ++ HsTerm.repr t2 p ++ " : " ++ repr t1 ++";;" ++ Std.Format.line ++ HsTerm.repr t3 p
| HsIte t1 t2 t3 t4, p =>
  "if!" ++ Nat.repr t1 ++ " ← " ++ HsTerm.repr t2 p ++
  "then" ++ Std.Format.line ++ HsTerm.repr t3 p ++
  "else" ++ Std.Format.line ++ HsTerm.repr t4 p
-- | HsType t , p => Term.repr t p

instance HsTerm_repr : Repr HsTerm where
  reprPrec a p := HsTerm.repr a p

notation:15 a " `@ " b => HsTerm.HsApp a b
notation:15 "`λ[" a "]" b => HsTerm.HsLam a b
prefix:max "#" => HsTerm.HsVar
notation:15 "if " p " ← " s " then " i " else " e => HsTerm.HsIte p s i e

namespace HsTerm
 @[simp]
 def size : HsTerm -> Nat
 | HsVar _ => 0
 | HsLam t1 t2 => Term.size t1 + size t2 + 1
 | HsApp t1 t2 => size t1 + size t2 + 1
 | HsLet t1 t2 t3 => Term.size t1 + size t2 + size t3 + 1
 | HsIte _ t2 t3 t4 => size t2 + size t3 + size t4 + 1
 -- | HsType t => Term.size t

  @[simp]
  def neutral_form : HsTerm -> Option (Nat × List HsTerm)
  | .HsVar x => .some (x, [])
  | .HsApp f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [a])
  | _ => .none
end HsTerm

instance sizeOf_HsTerm : SizeOf HsTerm where
  sizeOf := HsTerm.size

inductive HsJudgment : Ctx Term -> HsTerm -> Term -> Prop where
| var :
  Judgment .wf Γ () ->
  (Γ d@ x).get_type = .some T ->
  HsJudgment Γ (#x) T
--- Implicit arrow and ∀ introduction/elimination
| implicitArrI :
  HsJudgment (.empty :: Γ) t τ ->
  Γ ⊢ e : π ->
  HsJudgment Γ t (π -t> τ)
| implicitArrE :
  HsJudgment Γ t (π -t> τ) ->
  Γ ⊢ e : π ->
  HsJudgment Γ t (τ β[e])
| implicitAllI :
  HsJudgment (.kind A :: Γ) t τ ->
  Γ ⊢ A : ★ ->
  HsJudgment Γ t (∀[A] τ)
| implicitAllE :
  HsJudgment Γ t (∀[A] τ) ->
  Γ ⊢ A : ★ ->
  HsJudgment Γ t (τ β[A])
-- Term typing
| lam :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (A -t> B, ★) ->
  HsJudgment (.type A :: Γ) t B ->
  HsJudgment Γ (`λ[A] t) (A -t> B)
| app :
  HsJudgment Γ t1 (A -t> B) ->
  HsJudgment Γ t2 A ->
  B' = B β[A] ->
  HsJudgment Γ (t1 `@ t2) B'
| letterm :
  HsJudgment Γ t1 A ->
  HsJudgment (.type A :: Γ) t2 ([S] B) ->
  HsJudgment Γ (.HsLet A t1 t2) B
| ite :
  HsJudgment Γ #t1 A ->
  HsJudgment Γ t2 A ->
  HsJudgment Γ t3 B ->
  HsJudgment Γ t4 B' ->
  HsJudgment Γ (HsTerm.HsIte t1 t2 t3 t4) B


notation: 170 Γ:170 " ⊢s " t:170 " : " A:170 => HsJudgment Γ t A

inductive Compile : {Γ : Ctx Term} -> {τ : Term} -> (t : HsTerm) ->  Γ ⊢s t : τ -> Term -> Prop where
| var :
  ⊢ Γ ->
  (Γ d@ i).get_type = .some τ ->
  (j1 : Γ ⊢s (.HsVar i) : τ) ->
  Compile (.HsVar i) j1 (Term.var i)
| app :
  (j1 : Γ ⊢s t1 : (τ' -t> τ)) ->
  (j2 : Γ ⊢s t2 : τ') ->
  (j3 : Γ ⊢s (t1 `@ t2) : (τ β[t2'])) ->
  Compile t1 j1 t1' ->
  Compile t2 j2 t2' ->
  Compile (t1 `@ t2) j3 (t1' `@ t2')
| appev :
  (j1 : Γ ⊢s t1 : (π -t> τ)) -> -- Γ ⊢ t1 : F a => τ
  (ValidHeadVariable π Γ.is_opent) ->
  Γ ⊢ e : π ->
  Compile t1 j1 t1' ->
  (j2 : Γ ⊢s t1 : (τ β[e])) ->
  Compile t1 j2 (t1' `@ e)
| appt :
  (j1 : Γ ⊢s t1 : (∀[A]B)) -> -- Γ ⊢ t1 : ∀[A]τ
  Compile t1 j1 t1' ->
  Γ ⊢ τ : A ->
  (j2 : Γ ⊢s t1 : (B β[τ])) ->
  Compile t1 j2 (t1' `@t τ)
| lam :
  (j1 : (.type A :: Γ) ⊢s t1 : τ) ->
  (j2 : Γ ⊢s (.HsLam A t1) : (A -t> τ)) ->
  (Γ ⊢ (A -t> τ) : ★) ->
  Compile t1 j1 t1' ->
  Compile (`λ[A] t1) j2 (`λ[A] t1')
| letterm :
  Γ ⊢ A : ★ ->
  Γ ⊢ τ : ★ ->
  (j1 : Γ ⊢s t1 : A) ->
  Compile t1 j1 t1' ->
  (j2 : (.term A t1' :: Γ) ⊢s t2 : ([S]τ)) ->
  Compile t2 j2 t2' ->
  (j3 : Γ ⊢s (.HsLet A t1 t2) : τ) ->
  Compile (.HsLet A t1 t2) j3 (.letterm A t1' t2')
| ite :
  Γ ⊢ T : ★ ->
  Γ ⊢ R : ★ ->
  StableTypeMatch Γ A R ->
  PrefixTypeMatch Γ A B T ->
  ValidHeadVariable R Γ.is_datatype ->
  (Γ d@ p).is_ctor ->
  (j1 : Γ ⊢s #p : A) ->
  (j2 : Γ ⊢s s : R) ->
  (j3 : Γ ⊢s i : B) ->
  (j4 : Γ ⊢s e : T) ->
  (j5 : Γ ⊢s .HsIte p s i e : T) ->
  Compile #p j1 p' ->
  Compile s j2 s' ->
  Compile i j3 i' ->
  Compile e j4 e' ->
  Compile (.HsIte p s i e) j5 (.ite p' s' i' e')

notation:180 " ⟅ " t:180 " ⟆ " j:180 " ⟶  " t':180 => Compile t j t'

theorem compile_head_preserving :
  p = .HsVar i ->
  (j : Γ ⊢s p : τ) ->
  (Γ d@ i).is_ctor ->
  (⟅ p ⟆ j ⟶  p') ->
  ValidHeadVariable p' Γ.is_ctor := by
intro e j pctor c;
induction c;
all_goals (cases e)
case _ => unfold ValidHeadVariable; simp; assumption
case _ e _ _ _ _ _ _ ih =>
  replace ih := ih rfl pctor;
  unfold ValidHeadVariable at ih;
  cases ih; case _ w h =>
  cases h; case _ t1nf h =>
  unfold ValidHeadVariable; simp;
  exists w.fst;
  apply And.intro;
  apply Exists.intro (w.snd ++ [(.term, e)]);
  symm; rw[Option.bind_eq_some]; exists w;
  apply And.intro; symm; assumption; simp
  assumption
case _ e _ _ _ _ ih =>
  replace ih := ih rfl pctor;
  unfold ValidHeadVariable at ih;
  cases ih; case _ w h =>
  cases h; case _ t1nf h =>
  unfold ValidHeadVariable; simp;
  exists w.fst;
  apply And.intro;
  apply Exists.intro (w.snd ++ [(.type, e)]);
  symm; rw[Option.bind_eq_some]; exists w;
  apply And.intro; symm; assumption; simp
  assumption


theorem compile_type_preserving :
  (j : Γ ⊢s t : τ) ->
  (⟅ t ⟆ j ⟶  t') ->
  Γ ⊢ t' : τ := by
intro j1 j2;
induction j2;
case _ gt _ =>
  apply Judgment.var; assumption; symm; assumption
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
case _ j1 j2 c j3 =>
  apply Judgment.lam;
  case _ => cases j2; assumption
  assumption
  assumption
case _ j1 c1 j2 c2 j3 ih1 ih2 =>
  apply Judgment.letterm
  assumption;
  assumption;
  assumption;
  assumption;
case _ p _ _ _ _ _ _ _ _ _ _ _ _ vhv j1 j2 j3 j4 _ c1 c2 c3 c4 _ _ _ _ =>
  apply Judgment.ite;
  assumption;
  assumption;
  assumption;
  assumption;
  apply compile_head_preserving; rfl; apply vhv; apply c1;
  assumption;
  assumption;
  assumption;
  assumption;
  assumption
