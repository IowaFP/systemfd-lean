import Hs.HsJudgment
import SystemFD.Judgment

set_option maxHeartbeats 500000

inductive Compile : {Γ : Ctx HsTerm} -> {τ : HsTerm} -> (t : HsTerm) -> Γ ⊢s t : τ -> Term -> Prop where
------------------------------------
-- Types and kinds
-----------------------------------
| type :
  Compile `★ j1 ★
| kind :
  Compile `□ j1 □
| arrowk :
  Compile κ1 j1 κ1' ->
  Compile κ2 j2 κ2' ->
  Compile (κ1 `-k> κ2) j3 (κ1' -k> κ2')
------------------------------------
-- Implicits
-----------------------------------
| appev :
  (j1 : Γ ⊢s t1 : (π ⇒ τ)) -> -- Γ ⊢ t1 : F a => τ
  (HsValidHeadVariable π Γ.is_opent) ->
  (j0 : Γ ⊢s e : π) ->
  Compile e j0 e' ->
  Compile t1 j1 t1' ->
  (j2 : Γ ⊢s t1 : (τ β[e])) ->
  Compile t1 j2 (t1' `@ e')
| appt :
  (j0 : Γ ⊢s τ : A) ->
  Compile τ j0 τ' ->
  (j1 : Γ ⊢s t1 : (`∀{A}B)) -> -- Γ ⊢ t1 : ∀[A]τ
  Compile t1 j1 t1' ->
  (j2 : Γ ⊢s t1 : (B β[τ])) ->
  Compile t1 j2 (t1' `@t τ')
------------------------------------
-- Terms
-----------------------------------
| var :
  ⊢s Γ ->
  (Γ d@ i).get_type = .some τ ->
  (j1 : Γ ⊢s (.HsVar i) : τ) ->
  Compile (.HsVar i) j1 (Term.var i)
| app :
  (j1 : Γ ⊢s t1 : (τ' → τ)) ->
  (j2 : Γ ⊢s t2 : τ') ->
  (j3 : Γ ⊢s (t1 `• t2) : (τ β[t2])) ->
  Compile t1 j1 t1' ->
  Compile t2 j2 t2' ->
  Compile (t1 `• t2) j3 (t1' `@ t2')
| lam :
  (j0 : Γ ⊢s A : `★) ->
  Compile A j0 A' ->
  (j1 : (.type A :: Γ) ⊢s t1 : τ) ->
  (j2 : Γ ⊢s (`λ{A} t1) : (A → τ)) ->
  Compile t1 j1 t1' ->
  Compile (`λ{A} t1) j2 (`λ[A'] t1')
| letterm :
  (j0 : Γ ⊢s A : `★) ->
  Compile A j0 A' ->
  (j1 : Γ ⊢s t1 : A) ->
  Compile t1 j1 t1' ->
  (j2 : (.term A t1 :: Γ) ⊢s t2 : ([S]τ)) ->
  Compile t2 j2 t2' ->
  (j3 : Γ ⊢s (.HsLet A t1 t2) : τ) ->
  Compile (.HsLet A t1 t2) j3 (.letterm A' t1' t2')
| ite :
  (j1 : Γ ⊢s p : A) ->
  (j2 : Γ ⊢s s : R) ->
  (j3 : Γ ⊢s i : B) ->
  (j4 : Γ ⊢s e : T) ->
  (j5 : Γ ⊢s .HsIte p s i e : T) ->
  Compile p j1 p' ->
  Compile s j2 s' ->
  Compile i j3 i' ->
  Compile e j4 e' ->
  Compile (.HsIte p s i e) j5 (.ite p' s' i' e')

notation:180 " ⟅ " t:180 " ⟆ " j:180 " ⟶  " t':180 => Compile t j t'
