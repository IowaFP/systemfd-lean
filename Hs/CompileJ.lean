import Hs.HsJudgment

set_option maxHeartbeats 500000

@[simp]
abbrev CompileJArgs : HsVariant -> Ctx HsTerm -> Type
| .ctx => λ _ => Ctx Term
| .term => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢t w.fst : w.snd) × Term
| .kind => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢κ w.fst : w.snd) × Term
| .type => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢τ w.fst : w.snd) × Term

notation "⟨ " t "," τ ";" j "," t' "⟩" => (Sigma.mk (t, τ) j , t')

inductive CompileJ : (v : HsVariant) -> (Γ : Ctx HsTerm) -> CompileJArgs v Γ -> Prop where
-----------------------------------
--- Contexts
------------------------------------
| wfnil : CompileJ .ctx [] []
| wfempty :
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.empty :: Γ) (.empty :: Γ')
| wftype :
  (j : Γ ⊢τ A : `★) ->
  CompileJ .type Γ (⟨A, `★; j, A'⟩) ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.type A :: Γ) (.type A' :: Γ')
| wfkind :
  (j : Γ ⊢κ A : `□) ->
  CompileJ .kind Γ ⟨A, `□; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.kind A :: Γ) (.kind A' :: Γ')
| wfdatatype :
  (j : Γ ⊢κ A : `□) ->
  CompileJ .kind Γ ⟨A, `□; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.datatype A :: Γ) (.datatype A' :: Γ')
| wfctor :
  (j : Γ ⊢τ A : `★) ->
  CompileJ .type Γ ⟨A, `★; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.ctor A :: Γ) (.ctor A' :: Γ')
| wfterm :
  (j1 : Γ ⊢τ A : `★) ->
  (j2 : Γ ⊢t t1 : A) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .term Γ ⟨t1, A; j2, t1'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.term A t1 :: Γ) (.term A' t1' :: Γ')
------------------------------------
-- Types and kinds
-----------------------------------
| type :
  (j : Γ ⊢κ `★ : `□) ->
  CompileJ .kind Γ ⟨`★, `□; j, ★⟩
| arrowk :
  (j1 : Γ ⊢κ κ1 : `□) ->
  (j2 : Γ ⊢κ κ2 : `□) ->
  (j3 : Γ ⊢κ (κ1 `-k> κ2) : `□) ->
  CompileJ .kind Γ ⟨κ1, `□ ; j1 , κ1'⟩ ->
  CompileJ .kind Γ ⟨κ2, `□ ; j2 , κ2'⟩ ->
  CompileJ .kind Γ ⟨(κ1 `-k> κ2), `□; j3, (κ1' -k> κ2')⟩
| appk :
  (j1 : Γ ⊢τ A : (κ1 `-k> κ2)) ->
  (j2 : Γ ⊢τ B : κ1) ->
  (j3 : Γ ⊢τ (A `•k B) : κ2) ->
  (jk1 : Γ ⊢κ (κ1 `-k> κ2): `□) ->
  CompileJ .kind Γ ⟨κ1 `-k> κ2, `□; jk1, κ1' -k> κ2'⟩ ->
  CompileJ .kind Γ ⟨κ2, `□; jk2, κ2'⟩ ->
  CompileJ .type Γ ⟨A, (κ1 `-k> κ2) ; j1 , A'⟩ ->
  CompileJ .type Γ ⟨B,  κ1; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A `•k B), κ2; j3, (A' `@k B')⟩
| arrow :
  (j1 : Γ ⊢τ A : `★) ->
  (j2 : (.empty :: Γ) ⊢τ B : `★) ->
  (j3 : Γ ⊢τ (A → B) : `★) ->
  CompileJ .type Γ ⟨A, `★ ; j1 , A'⟩ ->
  CompileJ .type (.empty :: Γ) ⟨B, `★ ; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A → B), `★; j3, (A' -t> B')⟩
| farrow :
  (j1 : Γ ⊢τ A : `★) ->
  (j2 : (.empty :: Γ) ⊢τ B : `★) ->
  (j3 : Γ ⊢τ (A ⇒ B) : `★) ->
  CompileJ .type Γ ⟨A, `★ ; j1 , A'⟩ ->
  CompileJ .type (.empty :: Γ) ⟨B, `★ ; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A ⇒ B), `★; j3, (A' -t> B')⟩

-- ------------------------------------
-- -- Implicits
-- -----------------------------------
| appev :
  (j1 : Γ ⊢τ π : `★) ->
  (j2 : Γ ⊢τ (π ⇒ τ) : `★) ->
  (j3 : Γ ⊢t e : π) ->
  (j4 : Γ ⊢t t1 : (π ⇒ τ)) -> -- Γ ⊢ t1 : F a => τ
  (HsValidHeadVariable π Γ.is_opent) ->
  CompileJ .type Γ ⟨π, `★; j1, π'⟩ ->
  CompileJ .type Γ ⟨π ⇒ τ, `★; j2, π' -t> τ'⟩ ->
  CompileJ .term Γ ⟨e, π; j3, e'⟩ ->
  CompileJ .term Γ ⟨t1, (π ⇒ τ); j4, t1'⟩ ->
  τ'' = τ β[e] ->
  (j3 : Γ ⊢t t1 : τ'') ->
  CompileJ .term Γ ⟨t1, τ''; j3, (t1' `@ e')⟩
| lamev :
  (j1 : Γ ⊢τ π : `★) ->
  (j2 : Γ ⊢τ (π ⇒ τ) : `★) ->
  (j3 : Γ ⊢t t1 : (π ⇒ τ)) ->
  CompileJ .type Γ ⟨π, `★; j1, π'⟩ ->
  CompileJ .type Γ ⟨π ⇒ τ, `★; j2, π' -t> τ'⟩ ->
  CompileJ .term Γ ⟨t1, (π ⇒ τ); j3, (`λ[π']t1')⟩
| appt :
  (j1 : Γ ⊢τ τ : A) ->
  (j2 : Γ ⊢t t1 : (`∀{A}B)) -> -- Γ ⊢ t1 : ∀[A]τ
  (j3 : Γ ⊢t t1 : (B β[τ])) ->
  CompileJ .type Γ ⟨τ, A; j1, τ'⟩ ->
  CompileJ .term Γ ⟨t1,`∀{A}B; j2, t1'⟩ ->
  CompileJ .term Γ ⟨t1, B β[τ]; j3, (t1' `@t τ')⟩
| lamt :
  (j1 : Γ ⊢κ A : `□) ->
  (j2 : Γ ⊢τ (`∀{A}τ) : `★) ->
  (j3 : Γ ⊢t t : (`∀{A}τ)) ->
  CompileJ .kind Γ ⟨A, `□; j1, A'⟩ ->
  CompileJ .type Γ ⟨`∀{A}τ, `★; j2, ∀[A']τ'⟩ ->
  CompileJ .term Γ ⟨t, `∀{A}τ; j3, Λ[A']t'⟩

-- ------------------------------------
-- -- Terms
-- -----------------------------------
| var :
  ⊢s Γ ->
  (Γ d@ i).get_type = .some τ ->
  (j : Γ ⊢t (`#i) : τ) ->
  CompileJ .term Γ ⟨(.HsVar i), τ; j, #i⟩
| app :
  (j1 : Γ ⊢t t1 : (τ' → τ)) ->
  (j2 : Γ ⊢t t2 : τ') ->
  (j3 : Γ ⊢t (t1 `• t2) : (τ β[t2])) ->
  CompileJ .term Γ ⟨t1, (τ' → τ); j1, t1'⟩ ->
  CompileJ .term Γ ⟨t2, τ'; j2, t2'⟩ ->
  CompileJ .term Γ ⟨(t1 `• t2), τ β[t2]; j3, (t1' `@ t2')⟩
| lam :
  (j1 : Γ ⊢τ A : `★) ->
  (j2 : (.type A :: Γ) ⊢t t1 : τ) ->
  (j3 : Γ ⊢t (`λ{A} t1) : (A → τ)) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .term (.type A :: Γ)  ⟨t1, τ; j2, t1'⟩ ->
  CompileJ .term Γ ⟨(`λ{A} t1), A → τ; j3, (`λ[A'] t1')⟩
| letterm :
  (j1 : Γ ⊢τ A : `★) ->
  (j2 : Γ ⊢τ τ : `★) ->
  (j3 : Γ ⊢t t1 : A) ->
  (j4 : (.term A t1 :: Γ) ⊢t t2 : ([S]τ)) ->
  (j5 : Γ ⊢t (.HsLet A t1 t2) : τ) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .type Γ ⟨τ, `★; j2, τ'⟩ ->
  CompileJ .term Γ ⟨t1, A; j3, t1'⟩ ->
  CompileJ .term (.term A t1 :: Γ) ⟨t2, [S]τ; j4, t2'⟩ ->
  CompileJ .term Γ ⟨(.HsLet A t1 t2), τ; j5, (.letterm A' t1' t2')⟩
| ite :
  (j1 : Γ ⊢t p : A) ->
  (j2 : Γ ⊢t s : R) ->
  (j3 : Γ ⊢t i : B) ->
  (j4 : Γ ⊢t e : T) ->
  (j5 : Γ ⊢t .HsIte p s i e : T) ->
  CompileJ .term Γ ⟨p, A; j1, p'⟩ ->
  CompileJ .term Γ ⟨s, R; j2, s'⟩ ->
  CompileJ .term Γ ⟨i, B; j3, i'⟩ ->
  CompileJ .term Γ ⟨e, T; j4, e'⟩ ->
  CompileJ .term Γ ⟨(.HsIte p s i e), T; j5, (.ite p' s' i' e')⟩

-- notation:180 " ⟅ " j " ⟆ " j:180 " ⟶  " t':180 => CompileJ t j t'
