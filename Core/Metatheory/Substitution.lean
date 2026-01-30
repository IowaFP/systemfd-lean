import LeanSubst
import Core.Typing
import Core.Metatheory.Rename

open LeanSubst

theorem Kinding.subst_lift {Δ Δσ : List Kind} {σ : Subst Ty} T :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  ∀ i K, (T::Δ)[i]? = some K -> G&(T::Δσ) ⊢ σ.lift i : K
:= by
  intro h1 i K h2
  cases i <;> simp at *
  case _ => subst h2; apply var; simp
  case _ i =>
    replace h1 := h1 i K h2
    replace h1 := Kinding.weaken T h1
    simp at h1; exact h1

theorem Kinding.subst Δσ (σ : Subst Ty) :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  G&Δ ⊢ A : K ->
  G&Δσ ⊢ A[σ] : K
:= by
  intro h j
  induction j generalizing Δσ σ <;> simp
  case var Δ x K j => apply h x K j
  case global j => apply global j
  case arrow j1 j2 ih1 ih2 =>
    apply arrow
    apply ih1 _ _ h
    apply ih2 _ _ h
  case all K Δ P _ j ih =>
    replace ih := ih (K :: Δσ) σ.lift (subst_lift K h)
    simp at ih
    apply all ih
  case app j1 j2 ih1 ih2 =>
    apply app
    apply ih1 _ _ h
    apply ih2 _ _ h
  case eq j1 j2 ih1 ih2 =>
    apply eq
    apply ih1 _ _ h
    apply ih2 _ _ h

theorem Kinding.beta :
  G&(T::Δ) ⊢ A : K ->
  G&Δ ⊢ t : T ->
  G&Δ ⊢ A[su t::+0] : K
:= by
  intro j1 j2
  apply Kinding.subst Δ (su t::+0) _ j1
  intro i K h; cases i <;> simp at *
  case _ => subst h; exact j2
  case _ i => apply var h

theorem ValidHeadVariable.subst_type (σ : Subst Ty)
  : ValidHeadVariable t test -> ValidHeadVariable t[σ:Ty] test
:= by
  intro j
  rcases j with ⟨⟨x, sp⟩, e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[σ:Ty])); simp [*]
  have lem := Spine.apply_eq e1; rw [lem]
  simp

theorem ValidHeadVariable.subst (σ : Subst Term)
  : ValidHeadVariable t test -> ValidHeadVariable t[σ] test
:= by
  intro j
  rcases j with ⟨⟨x, sp⟩, e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[σ:Term])); simp [*]
  have lem := Spine.apply_eq e1; rw [lem]
  simp

theorem ValidTyHeadVariable.subst (σ : Subst Ty)
  : ValidTyHeadVariable t test -> ValidTyHeadVariable t[σ] test
:= by
  intro j
  rcases j with ⟨⟨x, sp⟩, e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[σ:Ty])); simp [*]
  have lem := Ty.Spine.apply_eq e1; rw [lem]
  simp

theorem StableTypeMatch.subst Δσ (σ : Subst Ty) :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  StableTypeMatch Δ A B ->
  StableTypeMatch Δσ A[σ] B[σ]
:= by
  intro h j
  induction j generalizing Δσ σ
  case refl R x Δ j =>
    rcases x with ⟨x, sp⟩
    apply refl (x := (x, sp.map (·[σ])))
    have lem := Ty.Spine.apply_eq j
    rw [lem]; simp
  case arrow j ih =>
    simp; apply arrow
    apply ih _ _ h
  case all K Δ B R j ih =>
    simp; apply all
    replace ih := ih (K::Δσ) σ.lift (Kinding.subst_lift K h)
    simp at ih; simp; exact ih

theorem PrefixTypeMatch.subst Δσ (σ : Subst Ty) :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  PrefixTypeMatch Δ A B C ->
  PrefixTypeMatch Δσ A[σ] B[σ] C[σ]
:= by
  intro h j
  induction j generalizing Δσ σ
  case refl B x Δ T j =>
    rcases x with ⟨x, sp⟩
    apply refl (x := (x, sp.map (·[σ])))
    have lem := Ty.Spine.apply_eq j
    rw [lem]; simp
  case arrow j ih =>
    simp; apply arrow
    apply ih _ _ h
  case all K Δ B V T j ih =>
    simp; apply all
    replace ih := ih (K::Δσ) σ.lift (Kinding.subst_lift K h)
    simp at ih; simp; exact ih

theorem Ty.spine_subst (Δ Δσ : List Kind) (σ: Subst Ty) (A : Ty) :
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  A.spine = .some (H, sp) ->
  A[r].spine = .some (H, sp.map (·[r])) := by
intro h j
induction A generalizing sp <;> simp at *
all_goals (try case _ => unfold spine at j; cases j)
case _ => unfold spine at j; simp at j; unfold spine; simp; assumption
case _ f a ih1 ih2 => cases j; case _ spf j =>
  cases j; case _ e1 h1 =>
  have ih1' := ih1 h1
  exists spf.map (·[r])
  rw[e1]; constructor;
  simp
  assumption

theorem Global.type_subst_noop (G : List Global) (p : String) (σ : Subst Ty) : ⊢ G ->
  ctor_ty p G = .some B ->
  B[σ] = B := by
intro wf h
unfold ctor_ty at h;
generalize ludef : lookup_type G p = lu at *
cases lu <;> simp at *
rcases h with ⟨h1, h2⟩
cases h2
apply GlobalWf.closed wf ludef


theorem Typing.subst_type Δσ (σ : Subst Ty) :
  ⊢ G ->
  (∀ i K, Δ[i]? = some K -> G&Δσ ⊢ σ i : K) ->
  G&Δ,Γ ⊢ t : A ->
  G&Δσ,Γ.map (·[σ]) ⊢ t[σ:Ty] : A[σ]
:= by
  intro wf h j; induction j generalizing Δσ σ <;> simp
  case var Γ x A Δ K j1 j2 =>
    apply var; simp
    apply Exists.intro _
    apply And.intro j1 rfl
    apply Kinding.subst _ σ h j2
  case global j1 j2 =>
    rw [GlobalWf.closed wf j1]
    replace j2 := Kinding.subst Δσ σ h j2
    rw [GlobalWf.closed wf j1] at j2
    apply global j1 j2
  case mtch _ s R c T A PTy ps cs _ vtyhv sJ ih1 _ ih3 _ ih5 ih6 ih7 ih8 ih9 =>
    apply mtch (A := λ i => (A i)[σ]) (PTy := λ i => (PTy i)[σ])
    apply ih6; assumption
    apply ValidTyHeadVariable.subst; assumption
    apply ih7; assumption
    intro i; replace ih1 := ih1 i; apply ValidHeadVariable.subst_type; assumption
    intro i; replace ih8 := ih8 i; apply ih8; assumption
    intro i; replace ih3 := ih3 i; apply StableTypeMatch.subst; assumption; assumption
    intro i; replace ih9 := ih9 i; apply ih9; assumption
    intro i; replace ih5 := ih5 i; apply PrefixTypeMatch.subst; assumption; assumption
  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    apply guard
    apply ih1 _ _ h
    apply ih2 _ _ h
    apply ih3 _ _ h
    apply ValidHeadVariable.subst_type σ j4
    apply ValidTyHeadVariable.subst σ j5
    apply StableTypeMatch.subst _ _ h j6
    apply PrefixTypeMatch.subst _ _ h j7
  case lam j1 j2 ih =>
    apply lam
    apply Kinding.subst _ _ h j1
    apply ih _ _ h
  case app j1 j2 j3 ih1 ih2 =>
    apply app
    apply Kinding.subst _ _ h j1
    apply ih1 _ _ h
    apply ih2 _ _ h
  case lamt K Δ t P Γ j ih =>
    replace ih := ih (K::Δσ) σ.lift (Kinding.subst_lift K h)
    simp at ih; apply lamt; simp
    unfold Function.comp at *; simp at *
    exact ih
  case appt f K P a P' j1 j2 j3 ih =>
    apply appt (K := K) (P := P[σ.lift])
    apply ih _ _ h
    apply Kinding.subst _ _ h j2
    rw [j3]; simp
  case cast j1 j2 ih1 ih2 =>
    apply cast
    apply ih1 _ _ h
    apply ih2 _ _ h
  case refl j =>
    apply refl
    apply Kinding.subst _ _ h j
  case sym j ih =>
    apply sym
    apply ih _ _ h
  case seq j1 j2 ih1 ih2 =>
    apply seq
    apply ih1 _ _ h
    apply ih2 _ _ h
  case appc j1 j2 ih1 ih2 =>
    apply appc
    apply ih1 _ _ h
    apply ih2 _ _ h
  case arrowc j1 j2 ih1 ih2 =>
    apply arrowc
    apply ih1 _ _ h
    apply ih2 _ _ h
  case fst j1 j2 j3 ih =>
    apply fst
    apply Kinding.subst _ _ h j1
    apply Kinding.subst _ _ h j2
    apply ih _ _ h
  case snd j1 j2 j3 ih =>
    apply snd
    apply Kinding.subst _ _ h j1
    apply Kinding.subst _ _ h j2
    apply ih _ _ h
  case allc K Δ t b A B Γ j ih =>
    replace ih := ih (K::Δσ) σ.lift (Kinding.subst_lift K h)
    simp at ih; apply allc; simp;
    unfold Function.comp at *; simp at *
    apply ih
  case apptc Δ Γ f K A B a C D A' B' j1 j2 j3 j4 ih1 ih2 =>
    apply apptc (A := A[σ.lift]) (B := B[σ.lift]) (C := C[σ]) (D := D[σ])
    apply ih1 _ _ h
    apply ih2 _ _ h
    rw [j3]; simp
    rw [j4]; simp
  case zero j =>
    apply zero
    apply Kinding.subst _ _ h j
  case choice j1 j2 j3 ih1 ih2 =>
    apply choice
    apply Kinding.subst _ _ h j1
    apply ih1 _ _ h
    apply ih2 _ _ h

theorem Typing.beta_type :
  ⊢ G ->
  G&(K::Δ),Γ ⊢ t : A ->
  G&Δ ⊢ a : K ->
  G&Δ,Γ.map (·[su a::+0]) ⊢ t[su a::+0:Ty] : A[su a::+0]
:= by
  intro wf j1 j2
  apply subst_type Δ (su a::+0) wf _ j1
  intro i T h
  cases i <;> simp at *
  case _ => subst h; exact j2
  case _ i => apply Kinding.var h

theorem Typing.subst_lift_type {Γ Γσ : List Ty} {σ : Subst Term} T :
  ⊢ G ->
  (∀ i A K, Γ[i]? = some A -> G&Δ ⊢ A : K -> G&Δ,Γσ ⊢ σ i : A) ->
  ∀ i A K, (Γ.map (·[+1]))[i]? = some A ->
    G&(T::Δ) ⊢ A : K ->
    G&(T::Δ),(Γσ.map (·[+1])) ⊢ (σ ◾ +1@Ty) i : A
:= by
  intro wf h1 i A K h2 h3
  cases i <;> simp at *
  case _ =>
    rcases h2 with ⟨a, e1, e2⟩; subst e2
    replace h1 := h1 0 a K e1 (by sorry)
    apply rename_type (T::Δ) (· + 1) wf _ h1
    intro i; cases i <;> simp
  case _ i =>
    rcases h2 with ⟨a, e1, e2⟩; subst e2
    replace h1 := h1 (i + 1) a K e1 sorry
    apply rename_type (T::Δ) (· + 1) wf _ h1
    intro i; cases i <;> simp

theorem Typing.subst_lift {Γ Γσ : List Ty} {σ : Subst Term} T :
  ⊢ G ->
  (∀ i A K, Γ[i]? = some A -> G&Δ ⊢ A : K -> G&Δ,Γσ ⊢ σ i : A) ->
  ∀ i A K, (T::Γ)[i]? = some A -> G&Δ ⊢ A : K -> G&Δ,(T::Γσ) ⊢ σ.lift i : A
:= by
  intro wf h1 i A K h2 h3
  cases i <;> simp at *
  case _ =>
    subst h2; apply var
    simp; apply h3
  case _ i =>
    replace h1 := h1 i A K h2 h3
    replace h1 := weaken T wf h1
    simp at h1; exact h1

theorem Typing.subst Γσ (σ : Subst Term) :
  ⊢ G ->
  (∀ i A K, Γ[i]? = some A -> G&Δ ⊢ A : K -> G&Δ,Γσ ⊢ σ i : A) ->
  G&Δ,Γ ⊢ t : A ->
  G&Δ,Γσ ⊢ t[σ] : A
:= by
  intro wf h j; induction j generalizing Γσ σ <;> simp
  case var Γ x A Δ K j1 j2 => apply h x A K j1 j2
  case global j1 j2 => apply global j1 j2
  case mtch c _ A PTy pats cs _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
    apply mtch (A := A) (PTy := PTy)
    apply ih6; apply h
    assumption
    apply ih7; apply h
    intro i; replace ih1 := ih1 i; apply ValidHeadVariable.subst; assumption
    intro i; apply ih8; assumption
    intro i; replace ih3 := ih3 i; assumption
    intro i; replace ih9 := ih9 i; apply ih9; assumption
    intro i; replace ih5 := ih5 i; assumption
  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    apply Typing.guard
    apply ih1 _ _ h
    apply ih2 _ _ h
    apply ih3 _ _ h
    apply ValidHeadVariable.subst σ j4
    apply j5; apply j6; apply j7
  case lam Δ A b Γ t B j1 j2 ih =>
    replace ih := ih (A::Γσ) σ.lift (subst_lift A wf h)
    simp at ih; apply lam j1 ih
  case app j1 j2 j3 ih1 ih2 =>
    apply app
    assumption
    apply ih1 _ _ h
    apply ih2 _ _ h
  case lamt j ih =>
    replace ih := ih (Γσ.map (·[+1])) (σ ◾ +1@Ty) (subst_lift_type _ wf h)
    apply lamt ih
  case appt j1 j2 j3 ih =>
    apply appt _ j2 j3
    apply ih _ _ h
  case cast j1 j2 ih1 ih2 =>
    apply cast
    apply ih1 _ _ h
    apply ih2 _ _ h
  case refl j => apply refl j
  case sym j ih =>
    apply sym
    apply ih _ _ h
  case seq j1 j2 ih1 ih2 =>
    apply seq
    apply ih1 _ _ h
    apply ih2 _ _ h
  case appc j1 j2 ih1 ih2 =>
    apply appc
    apply ih1 _ _ h
    apply ih2 _ _ h
  case arrowc j1 j2 ih1 ih2 =>
    apply arrowc
    apply ih1 _ _ h
    apply ih2 _ _ h
  case fst j1 j2 j3 ih =>
    apply fst j1 j2
    apply ih _ _ h
  case snd j1 j2 j3 ih =>
    apply snd j1 j2
    apply ih _ _ h
  case allc j ih =>
    replace ih := ih (Γσ.map (·[+1])) (σ ◾ +1@Ty) (subst_lift_type _ wf h)
    apply allc ih
  case apptc j1 j2 j3 j4 ih1 ih2 =>
    apply apptc
    apply ih1 _ _ h
    apply ih2 _ _ h
    apply j3
    apply j4
  case zero j => apply zero j
  case choice j1 j2 j3 ih1 ih2 =>
    apply choice j1
    apply ih1 _ _ h
    apply ih2 _ _ h

theorem Typing.beta :
  ⊢ G ->
  G&Δ,(A::Γ) ⊢ t : T ->
  G&Δ,Γ ⊢ a : A ->
  G&Δ,Γ ⊢ t[su a::+0] : T
:= by
  intro wf j1 j2
  apply subst Γ (su a::+0) wf _ j1
  intro i B K h1 h2
  cases i <;> simp at *
  case _ => subst h1; exact j2
  case _ i => apply var h1 h2
