import Hs.Algorithm
import Hs.Metatheory.Uniqueness

theorem compile_kind_uniqueness :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢κ t : τ) ->
  (j2 : Γ ⊢κ t : τ) ->
  compile_kind Γ t τ j1 = .some t1 ->
  compile_kind Γ t τ j2 = .some t2 ->
  t1 = t2 := by
intro h j1 j2 c1 c2
have lem := kinds_have_unique_judgments h j1 j2; cases lem;
rw[c1] at c2; injection c2

theorem compile_type_uniqueness :
  (∀ Γ (h1 h2 : ⊢s Γ), h1 = h2) ->
  (j1 : Γ ⊢τ τ : k) ->
  (j2 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j1 = .some t1 ->
  compile_type Γ τ k j2 = .some t2 ->
  t1 = t2
  := by
intro h j1 j2 c1 c2;
have lem := types_have_unique_judgments h j1 j2; cases lem;
rw[c1] at c2; injection c2;

@[simp]
abbrev CompilePreservesTypeShapeAll :  (v : HsVariant) -> Ctx HsTerm -> HsJudgmentArgs v -> Prop
| .type => λ Γ => λ (τ, k) => ∀ wA wτ cτ,
  τ = (`∀{wA} wτ) ->
  k = `★ ->
  (j3 : Γ ⊢τ τ : k) ->
  compile_type Γ τ k j3 = .some cτ ->
  ∃ A' τ', cτ = ∀[A']τ'
| _ => λ _ => λ _ => true

theorem comile_preserves_type_shape_all_lemma :
  HsJudgment v Γ idx -> CompilePreservesTypeShapeAll v Γ idx
 := by
intro j; induction j <;> simp at *;
intro wA wτ cτ e1 e2 j3 c3;
cases j3; case _ hka hkb =>
unfold compile_type at c3; simp at c3;
rw[Option.bind_eq_some] at c3;
cases c3; case _ A' c3 =>
cases c3; case _ cA c4 =>
rw[Option.bind_eq_some] at c4;
cases c4; case _ B' c4 =>
cases c4; case _ cB e =>
cases e; simp;

theorem compile_preserves_type_shape_all :
  (j : Γ ⊢τ (`∀{A}τ) : `★) ->
  compile_type Γ (`∀{A}τ) `★ j = .some cτ ->
  ∃ A' τ', cτ = ∀[A']τ' := by
intro j c;
have lem := comile_preserves_type_shape_all_lemma j; simp at lem;
apply @lem A τ cτ rfl rfl j c

theorem compile_preserves_type_shape_arrow :
  (j1 : Γ ⊢τ (A → B) : `★) ->
  compile_type Γ (A → B) `★ j1 = .some cτ ->
  ∃ (A' : Term)  (B' : Term) (j2 : Γ ⊢τ A : `★) (j3 : (.empty :: Γ) ⊢τ B : `★),
        cτ = (A' -t> B')
         ∧ (compile_type Γ A `★ j2 = .some A')
         ∧ (compile_type (.empty::Γ) B `★ j3 = .some B')  := by
intro j1 j2;
unfold compile_type at j2; cases j1; simp at j2;
rw[Option.bind_eq_some] at j2;
cases j2; case _ A' j2 =>
cases j2; case _ j2 j3 =>
rw[Option.bind_eq_some] at j3;
cases j3; case _ B' j3 =>
cases j3; case _ j3 e =>
cases e; case _ ja jb =>
exists A'; exists B'; exists ja; exists jb;


theorem compile_preserves_type_shape_farrow :
  (j1 : Γ ⊢τ (A ⇒ B) : `★) ->
  compile_type Γ (A ⇒ B) `★ j1 = .some cτ ->
  ∃ (A' : Term)  (B' : Term) (j2 : Γ ⊢τ A : `★) (j3 : (.empty :: Γ) ⊢τ B : `★),
        cτ = (A' -t> B')
         ∧ (compile_type Γ A `★ j2 = .some A')
         ∧ (compile_type (.empty::Γ) B `★ j3 = .some B')  := by
intro j1 j2;
unfold compile_type at j2; cases j1; simp at j2;
rw[Option.bind_eq_some] at j2;
cases j2; case _ A' j2 =>
cases j2; case _ j2 j3 =>
rw[Option.bind_eq_some] at j3;
cases j3; case _ B' j3 =>
cases j3; case _ j3 e =>
cases e; case _ ja _ jb =>
exists A'; exists B'; exists ja; exists jb
