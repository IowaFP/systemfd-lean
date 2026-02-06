import LeanSubst
import Core.Typing

import Core.Util

open LeanSubst

theorem subst_lift [RenMap T] (σ : Subst T) :
  x < n ->
  rep Subst.lift σ n x = re x
:= by
  intro h; induction n generalizing x σ <;> simp [rep]
  cases h
  case _ n ih =>
  cases x <;> simp [Subst.lift]
  case _ i =>
  have lem : i < n := by omega
  replace ih := @ih i σ lem
  rw [ih]

theorem Kinding.closed_rep :
  G&Δ ⊢ A : K ->
  ∀ (σ : Subst Ty), A[rep Subst.lift σ Δ.length:_] = A
:= by
  intro j; induction j <;> intro σ <;> simp
  case var Δ x K j =>
    have lem : x < Δ.length := Δ.indexing_length_some j
    rw [subst_lift σ lem]; simp
  case arrow ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp
  case all ih =>
    replace ih := ih σ
    simp at ih; exact ih
  case app ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp
  case eq ih1 ih2 =>
    rw [ih1 σ, ih2 σ]; simp

theorem Kinding.closed : G&[] ⊢ A : K -> ∀ σ, A[σ] = A := by
  intro j; apply closed_rep j

theorem ValidInstTy.closed : ValidInstTy G x Δ T -> ∃ b, G&Δ ⊢ T : .base b := by
  intro h; induction h <;> simp at *
  case _ => exists b◯
  case _ ih =>
    exists b★
    constructor; assumption
  case _ ih =>
    cases ih; case _ b ih =>
    exists b★
    constructor; assumption; assumption


theorem GlobalWf.head {G : List Global} : ⊢ (g :: G) -> GlobalWf G g := by
  intro j; cases j; case _ j => exact j

theorem GlobalWf.tail {G : List Global} : ⊢ (g :: G) -> ⊢ G := by
  intro j; cases j; case _ j _ => exact j

theorem GlobalWf.closed_ctors :
  ((Option.map Entry.type d).get! = some T -> ∀ σ, T[σ] = T) ->
  (∀ i e, v i = some e -> e.type = some T -> ∀ σ, T[σ] = T) ->
  (Option.map Entry.type (Vec.fold Option.or d v)).get! = some T ->
  ∀ σ, T[σ] = T
:= by
  intro h1 h2 h3
  induction v using Vec.induction <;> simp at h3
  case nc => apply h1 h3
  case cc t v ih =>
    cases t <;> simp at h3
    case _ =>
      apply ih _ h3
      intro i en e1 e2
      replace h2 := h2 (Fin.succ i) en (by simp; exact e1) e2
      apply h2
    case _ en =>
      apply h2 0 _ _ h3; simp

theorem GlobalWf.closed {G : List Global} :
  ⊢ G ->
  lookup_type G x = some T ->
  ∀ σ, T[σ] = T
:= by
  intro j h
  unfold lookup_type at h
  fun_induction lookup
  all_goals try solve | simp [Entry.type] at h
  all_goals try solve | case _ ih => apply ih (tail j) h
  case _ n y K cs1 tl cs2 e ih =>
    have lem := head j
    cases lem; case _ ctors =>
    apply closed_ctors (ih (tail j)) _ h
    intro i e q1 q2
    subst cs2; simp at q1; rcases q1 with ⟨e1, e2⟩
    generalize zdef : cs1 i = z at *
    rcases z with ⟨y, T'⟩; simp at *; subst e1 e2
    simp [Entry.type] at q2; subst q2
    replace ctors := ctors i x T' (by rw [zdef])
    apply Kinding.closed ctors.1
  case _ y T tl e =>
    replace e := LawfulBEq.eq_of_beq e
    simp [Entry.type] at h; subst e h
    have lem := head j
    cases lem ; case _ j =>
    apply Kinding.closed j
  case _ y T b tl e =>
    replace e := LawfulBEq.eq_of_beq e
    simp [Entry.type] at h; subst e h
    have lem := head j
    cases lem; case _ j1 j2 =>
    apply Kinding.closed j1
  case _ y T tl e =>
    replace e := LawfulBEq.eq_of_beq e
    simp [Entry.type] at h; subst e h
    cases j; case _ wf j =>
    cases j; case _ j =>
    have lemj : ∃ b, (tl&[] ⊢ T : .base b) := by
      apply ValidInstTy.closed j
    cases lemj; case _ lemj =>
    apply Kinding.closed lemj

theorem Kinding.rename_lift {Δ Δr : List Kind} K (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  ∀ i, (K::Δ)[i]? = (K::Δr)[r.lift i]?
:= by
  intro h i
  cases i <;> simp [Ren.lift] at *
  case _ i => exact h i

theorem Kinding.rename Δr (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  G&Δ ⊢ A : K ->
  G&Δr ⊢ A[r] : K
:= by
  intro h j
  induction j generalizing Δr r <;> simp
  case var Δ x K j =>
    simp [Ren.to]; apply Kinding.var
    rw [h x] at j; exact j
  case global j => apply Kinding.global j
  case arrow ih1 ih2 => apply Kinding.arrow (ih1 _ _ h) (ih2 _ _ h)
  case all K Δ P j ih =>
    replace ih := ih (K::Δr) r.lift (rename_lift K r h)
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    apply Kinding.all ih
  case app ih1 ih2 => apply Kinding.app (ih1 _ _ h) (ih2 _ _ h)
  case eq ih1 ih2 => apply Kinding.eq (ih1 _ _ h) (ih2 _ _ h)

theorem Kinding.weaken T : G&Δ ⊢ A : K -> G&(T::Δ) ⊢ A[+1] : K := by
  intro j; apply rename (T::Δ) (· + 1) _ j
  intro i; cases i <;> simp

theorem ValidHeadVariable.rename_type (r : Ren)
  : ValidHeadVariable t test -> ValidHeadVariable t[r:Ty] test
:= by
  intro j; cases j; case _ u e =>
  rcases u with ⟨x, sp⟩
  rcases e with ⟨e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[r:Ty])); rw [e2]; simp
  have lem := Spine.apply_eq e1
  rw [lem]; simp

theorem ValidHeadVariable.rename (r : Ren)
  : ValidHeadVariable t test -> ValidHeadVariable t[r:Term] test
:= by
  intro j; cases j; case _ u e =>
  rcases u with ⟨x, sp⟩
  rcases e with ⟨e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[r:Term])); rw [e2]; simp
  have lem := Spine.apply_eq e1
  rw [lem]; simp

theorem ValidTyHeadVariable.rename (r : Ren) :
  ValidTyHeadVariable t test -> ValidTyHeadVariable t[r] test
:= by
  intro j; cases j; case _ u e =>
  rcases u with ⟨x, sp⟩
  rcases e with ⟨e1, e2⟩; simp at e2
  apply Exists.intro (x, sp.map (·[r])); rw [e2]; simp
  have lem := Ty.Spine.apply_eq e1
  rw [lem]; simp

theorem StableTypeMatch.rename Δr (r : Ren) :
  StableTypeMatch Δ A B ->
  StableTypeMatch Δr A[r] B[r]
:= by
  intro j
  induction j generalizing Δr r
  case refl R x Δ j =>
    rcases x with ⟨x, sp⟩
    apply refl (x := (x, sp.map (·[r])))
    have lem := Ty.Spine.apply_eq j
    rw [lem]; simp
  case arrow j ih =>
    simp; apply arrow
    apply ih _ _
  case all K Δ B R j ih =>
    simp; apply all
    replace ih := ih (K::Δr) r.lift
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    simp; exact ih

theorem PrefixTypeMatch.rename Δr (r : Ren) {A : Ty} :
  PrefixTypeMatch Δ A B C ->
  PrefixTypeMatch Δr A[r] B[r] C[r]
:= by
  intro j
  induction j generalizing Δr r
  case refl B x Δ T j =>
    rcases x with ⟨x, sp⟩
    apply refl (x := (x, sp.map (·[r])))
    have lem := Ty.Spine.apply_eq j
    rw [lem]; simp
  case arrow j ih =>
    simp; apply arrow
    apply ih _ _
  case all K Δ B V T j ih =>
    simp; apply all
    replace ih := ih (K::Δr) r.lift
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    simp; exact ih

theorem Ty.spine_rename (Δ Δr : List Kind) (r: Ren) (A : Ty) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
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

theorem Global.type_rename_noop (G : List Global) (p : String) (r : Ren) : ⊢ G ->
  ctor_ty p G = .some B ->
  B[r] = B := by
intro wf h
unfold ctor_ty at h
generalize ludef : lookup_type G p = lu at *
cases lu <;> simp at *
rcases h with ⟨h1, h2⟩; cases h2
apply GlobalWf.closed wf ludef

theorem Typing.rename_type Δr (r : Ren) :
  ⊢ G ->
  (∀ i, Δ[i]? = Δr[r i]?) ->
  G&Δ,Γ ⊢ t : A ->
  G&Δr,Γ.map (·[r]) ⊢ t[r:Ty] : A[r]
:= by
  intro wf h j; induction j generalizing Δr r <;> simp
  case var j1 j2 =>
    apply var
    simp; apply Exists.intro _
    apply And.intro j1 rfl
    apply Kinding.rename _ r h j2
  case global j1 j2 =>
    rw [GlobalWf.closed wf j1]
    replace j2 := Kinding.rename Δr r h j2
    rw [GlobalWf.closed wf j1] at j2
    apply global j1 j2
  case mtch _ s R c T A PTy ps cs _ vtyhv sJ ih1 _ ih3 _ ih5 ih6 ih7 ih8 ih9 =>
    apply mtch (CTy := λ i => (A i)[r]) (PTy := λ i => (PTy i)[r])
    apply ih6; assumption
    apply ValidTyHeadVariable.rename; assumption
    apply ih7; assumption
    intro i; replace ih1 := ih1 i; apply ValidHeadVariable.rename_type; assumption
    intro i; replace ih8 := ih8 i; apply ih8; assumption
    intro i; replace ih3 := ih3 i; apply StableTypeMatch.rename; assumption
    intro i; replace ih9 := ih9 i Δr r h; assumption
    intro i; replace ih5 := ih5 i; apply PrefixTypeMatch.rename; assumption
  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    apply guard
    apply ih1 _ _ h
    apply ih2 _ _ h
    apply ih3 _ _ h
    apply ValidHeadVariable.rename_type r j4
    apply ValidTyHeadVariable.rename r j5
    apply StableTypeMatch.rename _ _ j6
    apply PrefixTypeMatch.rename _ _ j7
  case lam j1 j2 ih =>
    apply lam
    apply Kinding.rename _ _ h j1
    apply ih _ _ h
  case app j1 j2 j3 ih1 ih2 =>
    apply app
    apply Kinding.rename _ _ h j1
    apply ih1 _ _ h
    apply ih2 _ _ h
  case lamt Δ K P t Γ jk j ih =>
    replace ih := ih (K::Δr) r.lift (Kinding.rename_lift K r h)
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    apply lamt;
    case _ => have lem := Kinding.rename _ _ h jk; simp at lem; exact lem
    case _ => simp; unfold Function.comp at *; simp at *;  exact ih
  case appt f K P a P' j1 j2 j3 ih =>
    apply appt (K := K) (P := P[r.lift])
    rw [Ren.to_lift (S := Ty)]
    apply ih _ _ h
    apply Kinding.rename _ _ h j2
    rw [Ren.to_lift (S := Ty), j3]; simp
  case cast j1 j2 ih1 ih2 =>
    apply cast
    apply ih1 _ _ h
    apply ih2 _ _ h
  case refl j =>
    apply refl
    apply Kinding.rename _ _ h j
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
    apply Kinding.rename _ _ h j1
    apply Kinding.rename _ _ h j2
    apply ih _ _ h
  case snd j1 j2 j3 ih =>
    apply snd
    apply Kinding.rename _ _ h j1
    apply Kinding.rename _ _ h j2
    apply ih _ _ h
  case allc K Δ t A B Γ j ih =>
    replace ih := ih (K::Δr) r.lift (Kinding.rename_lift K r h)
    rw [Ren.to_lift (S := Ty)] at ih; simp at ih
    apply allc; simp; unfold Function.comp at *; simp at *
    apply ih
  case apptc Δ Γ f K A B a C D A' B' j1 j2 j3 j4 ih1 ih2 =>
    apply apptc (A := A[r.lift]) (B := B[r.lift]) (C := C[r]) (D := D[r])
    rw [Ren.to_lift (S := Ty)]
    apply ih1 _ _ h
    apply ih2 _ _ h
    rw [Ren.to_lift (S := Ty), j3]; simp
    rw [Ren.to_lift (S := Ty), j4]; simp
  case zero j =>
    apply zero
    apply Kinding.rename _ _ h j
  case choice j1 j2 j3 ih1 ih2 =>
    apply choice
    apply Kinding.rename _ _ h j1
    apply ih1 _ _ h
    apply ih2 _ _ h

theorem Typing.rename_lift_type {Γ Γr : List Ty} (r : Ren) :
  (∀ {i A}, Γ[i]? = some A -> Γr[r i]? = some A) ->
  ∀ {i A}, (Γ.map (·[+1]))[i]? = some A -> (Γr.map (·[+1]))[r i]? = some A
:= by
  intro h1 i A h2
  cases Γr <;> simp at *
  case _ =>
    rcases h2 with ⟨a, e1, e2⟩; subst e2
    apply h1 e1
  case _ hd tl =>
    generalize kdef : r i = k at *
    rcases h2 with ⟨a, e1, e2⟩; subst e2
    cases k <;> simp at *
    case _ =>
      replace h1 := @h1 i a e1
      rw [kdef] at h1; simp at h1
      subst h1; rfl
    case _ k =>
      replace h1 := @h1 i a e1
      rw [kdef] at h1; simp at h1
      apply Exists.intro a; simp [*]

theorem Typing.rename_lift {Γ Γr : List Ty} (r : Ren) T :
  (∀ {i A}, Γ[i]? = some A -> Γr[r i]? = some A) ->
  ∀ {i A}, (T::Γ)[i]? = some A -> (T::Γr)[r.lift i]? = some A
:= by
  intro h1 i A h2
  cases i <;> simp [Ren.lift] at *
  case _ => exact h2
  case _ i => apply h1 h2

theorem Typing.rename Γr (r : Ren) :
  ⊢ G ->
  (∀ {i A}, Γ[i]? = some A -> Γr[r i]? = some A) ->
  G&Δ,Γ ⊢ t : A ->
  G&Δ,Γr ⊢ t[r] : A
:= by
  intro wf h j; induction j generalizing Γr r <;> simp
  case var j1 j2 => simp [Ren.to]; apply Typing.var (h j1) j2
  case global j1 j2 => apply Typing.global j1 j2
  case mtch c _ A PTy pats cs _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
    apply mtch (CTy := A) (PTy := PTy)
    apply ih6; apply h
    assumption
    apply ih7; apply h
    intro i; replace ih1 := ih1 i; apply ValidHeadVariable.rename; assumption
    intro i; apply ih8; assumption
    intro i; replace ih3 := ih3 i; assumption
    intro i; replace ih9 := ih9 i; apply ih9; assumption
    intro i; replace ih5 := ih5 i; assumption

  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    apply Typing.guard
    apply ih1 _ _ h
    apply ih2 _ _ h
    apply ih3 _ _ h
    apply ValidHeadVariable.rename r j4
    apply j5; apply j6; apply j7
  case lam Δ A b Γ t B j1 j2 ih =>
    replace ih := ih (A::Γr) r.lift (rename_lift r A h)
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    apply lam j1 ih
  case app j1 j2 j3 ih1 ih2 =>
    apply app j1
    apply ih1 _ _ h
    apply ih2 _ _ h
  case lamt j h ih =>
    apply lamt
    apply j
    apply ih _ _ (rename_lift_type r h)
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
    apply allc
    apply ih _ _ (rename_lift_type r h)
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

theorem Typing.weaken T : ⊢ G -> G&Δ,Γ ⊢ t : A -> G&Δ,(T::Γ) ⊢ t[+1] : A := by
  intro wf j; apply rename (T::Γ) (· + 1) wf _ j; simp
