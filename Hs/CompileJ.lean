import Hs.HsJudgment

set_option maxHeartbeats 500000

inductive CompileVariant where -- what i am compiling?
| kind | type | term | ctx

@[simp]
abbrev CompileJArgs : CompileVariant -> Ctx HsTerm -> Type
| .ctx => λ _ => Ctx Term
| .term => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢s w.fst : w.snd) × Term
| .kind => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢s w.fst : w.snd) × Term
| .type => λ Γ => ((w : (HsTerm × HsTerm)) × Γ ⊢s w.fst : w.snd) × Term

notation "⟨ " t "," τ ";" j "," t' "⟩" => (Sigma.mk (t, τ) j , t')

inductive CompileJ : (v : CompileVariant) -> (Γ : Ctx HsTerm) -> CompileJArgs v Γ -> Prop where
-----------------------------------
--- Contexts
------------------------------------
| wfnil : CompileJ .ctx [] []
| wfempty :
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.empty :: Γ) (.empty :: Γ')
| wftype :
  (j : Γ ⊢s A : `★) ->
  CompileJ .type Γ (⟨A, `★; j, A'⟩) ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.type A :: Γ) (.type A' :: Γ')
| wfkind :
  (j : Γ ⊢s A : `□) ->
  CompileJ .kind Γ ⟨A, `□; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.kind A :: Γ) (.kind A' :: Γ')
| wfdatatype :
  (j : Γ ⊢s A : `□) ->
  CompileJ .kind Γ ⟨A, `□; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.datatype A :: Γ) (.datatype A' :: Γ')
| wfctor :
  (j : Γ ⊢s A : `★) ->
  CompileJ .type Γ ⟨A, `★; j, A'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.ctor A :: Γ) (.ctor A' :: Γ')
| wfterm :
  (j1 : Γ ⊢s A : `★) ->
  (j2 : Γ ⊢s t1 : A) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .term Γ ⟨t1, A; j2, t1'⟩ ->
  CompileJ .ctx Γ Γ' ->
  CompileJ .ctx (.term A t1 :: Γ) (.term A' t1' :: Γ')
------------------------------------
-- Types and kinds
-----------------------------------
| type :
  (j : Γ ⊢s `★ : `□) ->
  CompileJ .kind Γ ⟨`★, `□; j, ★⟩
| arrowk :
  (j1 : Γ ⊢s κ1 : `□) ->
  (j2 : Γ ⊢s κ2 : `□) ->
  (j3 : Γ ⊢s (κ1 `-k> κ2) : `□) ->
  CompileJ .kind Γ ⟨κ1, `□ ; j1 , κ1'⟩ ->
  CompileJ .kind Γ ⟨κ2, `□ ; j2 , κ2'⟩ ->
  CompileJ .kind Γ ⟨(κ1 `-k> κ2), `□; j3, (κ1' -k> κ2')⟩
| appk :
  (j1 : Γ ⊢s A : (κ1 `-k> κ2)) ->
  (j2 : Γ ⊢s B : κ1) ->
  (j3 : Γ ⊢s (A `•k B) : κ2) ->
  (jk1 : Γ ⊢s (κ1 `-k> κ2): `□) ->
  CompileJ .kind Γ ⟨κ1 `-k> κ2, `□; jk1, κ1' -k> κ2'⟩ ->
  CompileJ .kind Γ ⟨κ2, `□; jk2, κ2'⟩ ->
  CompileJ .type Γ ⟨A, (κ1 `-k> κ2) ; j1 , A'⟩ ->
  CompileJ .type Γ ⟨B,  κ1; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A `•k B), κ2; j3, (A' `@k B')⟩
| arrow :
  (j1 : Γ ⊢s A : `★) ->
  (j2 : (.empty :: Γ) ⊢s B : `★) ->
  (j3 : Γ ⊢s (A → B) : `★) ->
  CompileJ .type Γ ⟨A, `★ ; j1 , A'⟩ ->
  CompileJ .type (.empty :: Γ) ⟨B, `★ ; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A → B), `★; j3, (A' -t> B')⟩
| farrow :
  (j1 : Γ ⊢s A : `★) ->
  (j2 : (.empty :: Γ) ⊢s B : `★) ->
  (j3 : Γ ⊢s (A ⇒ B) : `★) ->
  CompileJ .type Γ ⟨A, `★ ; j1 , A'⟩ ->
  CompileJ .type (.empty :: Γ) ⟨B, `★ ; j2 , B'⟩ ->
  CompileJ .type Γ ⟨(A ⇒ B), `★; j3, (A' -t> B')⟩

-- ------------------------------------
-- -- Implicits
-- -----------------------------------
| appev :
  (j1 : Γ ⊢s π : `★) ->
  (j2 : Γ ⊢s (π ⇒ τ) : `★) ->
  (j3 : Γ ⊢s e : π) ->
  (j4 : Γ ⊢s t1 : (π ⇒ τ)) -> -- Γ ⊢ t1 : F a => τ
  (HsValidHeadVariable π Γ.is_opent) ->
  CompileJ .type Γ ⟨π, `★; j1, π'⟩ ->
  CompileJ .type Γ ⟨π ⇒ τ, `★; j2, π' -t> τ'⟩ ->
  CompileJ .term Γ ⟨e, π; j3, e'⟩ ->
  CompileJ .term Γ ⟨t1, (π ⇒ τ); j4, t1'⟩ ->
  τ'' = τ β[e] ->
  (j3 : Γ ⊢s t1 : τ'') ->
  CompileJ .term Γ ⟨t1, τ''; j3, (t1' `@ e')⟩
| lamev :
  (j1 : Γ ⊢s π : `★) ->
  (j2 : Γ ⊢s (π ⇒ τ) : `★) ->
  (j3 : Γ ⊢s t1 : (π ⇒ τ)) ->
  CompileJ .type Γ ⟨π, `★; j1, π'⟩ ->
  CompileJ .type Γ ⟨π ⇒ τ, `★; j2, π' -t> τ'⟩ ->
  CompileJ .term Γ ⟨t1, (π ⇒ τ); j3, (`λ[π']t1')⟩
| appt :
  (j1 : Γ ⊢s τ : A) ->
  (j2 : Γ ⊢s t1 : (`∀{A}B)) -> -- Γ ⊢ t1 : ∀[A]τ
  (j3 : Γ ⊢s t1 : (B β[τ])) ->
  CompileJ .type Γ ⟨τ, A; j1, τ'⟩ ->
  CompileJ .term Γ ⟨t1,`∀{A}B; j2, t1'⟩ ->
  CompileJ .term Γ ⟨t1, B β[τ]; j3, (t1' `@t τ')⟩
| lamt :
  (j1 : Γ ⊢s A : `□) ->
  (j2 : Γ ⊢s (`∀{A}τ) : `★) ->
  (j3 : Γ ⊢s t1 : (`∀{A}τ)) ->
  CompileJ .kind Γ ⟨A, `□; j1, A'⟩ ->
  CompileJ .type Γ ⟨`∀{A}τ, `★; j2, ∀[A']τ' ⟩ ->
  CompileJ .term Γ ⟨t1, `∀{A}τ; j3, ∀[A']τ'⟩

-- ------------------------------------
-- -- Terms
-- -----------------------------------
| var :
  ⊢s Γ ->
  (Γ d@ i).get_type = .some τ ->
  (j : Γ ⊢s (.HsVar i) : τ) ->
  CompileJ .term Γ ⟨(.HsVar i), τ; j, #i⟩
| app :
  (j1 : Γ ⊢s t1 : (τ' → τ)) ->
  (j2 : Γ ⊢s t2 : τ') ->
  (j3 : Γ ⊢s (t1 `• t2) : (τ β[t2])) ->
  CompileJ .term Γ ⟨t1, (τ' → τ); j1, t1'⟩ ->
  CompileJ .term Γ ⟨t2, τ'; j2, t2'⟩ ->
  CompileJ .term Γ ⟨(t1 `• t2), τ β[t2]; j3, (t1' `@ t2')⟩
| lam :
  (j1 : Γ ⊢s A : `★) ->
  (j2 : (.type A :: Γ) ⊢s t1 : τ) ->
  (j3 : Γ ⊢s (`λ{A} t1) : (A → τ)) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .term (.type A :: Γ)  ⟨t1, τ; j2, t1'⟩ ->
  CompileJ .term Γ ⟨(`λ{A} t1), A → τ; j3, (`λ[A'] t1')⟩
| letterm :
  (j1 : Γ ⊢s A : `★) ->
  (j2 : Γ ⊢s τ : `★) ->
  (j3 : Γ ⊢s t1 : A) ->
  (j4 : (.term A t1 :: Γ) ⊢s t2 : ([S]τ)) ->
  (j5 : Γ ⊢s (.HsLet A t1 t2) : τ) ->
  CompileJ .type Γ ⟨A, `★; j1, A'⟩ ->
  CompileJ .type Γ ⟨τ, `★; j2, τ'⟩ ->
  CompileJ .term Γ ⟨t1, A; j3, t1'⟩ ->
  CompileJ .term (.term A t1 :: Γ) ⟨t2, [S]τ; j4, t2'⟩ ->
  CompileJ .term Γ ⟨(.HsLet A t1 t2), τ; j5, (.letterm A' t1' t2')⟩
| ite :
  (j1 : Γ ⊢s p : A) ->
  (j2 : Γ ⊢s s : R) ->
  (j3 : Γ ⊢s i : B) ->
  (j4 : Γ ⊢s e : T) ->
  (j5 : Γ ⊢s .HsIte p s i e : T) ->
  CompileJ .term Γ ⟨p, A; j1, p'⟩ ->
  CompileJ .term Γ ⟨s, R; j2, s'⟩ ->
  CompileJ .term Γ ⟨i, B; j3, i'⟩ ->
  CompileJ .term Γ ⟨e, T; j4, e'⟩ ->
  CompileJ .term Γ ⟨(.HsIte p s i e), T; j5, (.ite p' s' i' e')⟩

-- notation:180 " ⟅ " j " ⟆ " j:180 " ⟶  " t':180 => CompileJ t j t'
