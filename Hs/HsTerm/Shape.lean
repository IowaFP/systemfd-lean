import Hs.HsTerm.Definition
import Hs.HsTerm.Substitution
import Hs.HsCtx

namespace HsTerm

  inductive IsKind : HsTerm -> Prop where
  | type : IsKind `★
  | arrow : IsKind A -> IsKind B -> IsKind (A `-k> B)

  -- inductive IsType : HsCtx HsTerm -> HsTerm -> Prop where
  -- | var : IsType Γ `#x
  -- | all : IsKind A -> IsType (.kind A :: Γ) B -> IsType Γ (`∀{A} B)
  -- | arrow : IsType Γ A -> IsType (.empty :: Γ) B -> IsType Γ (A → B)
  -- | farrow : IsType Γ A -> IsType (.empty :: Γ) B -> IsType Γ (A ⇒ B)
  -- | app : IsType Γ A -> IsType Γ B -> IsType Γ (f `•k a)

  inductive IsType : HsTerm -> Prop where
  | var : IsType `#x
  | all : IsKind A -> IsType B -> IsType (`∀{A} B)
  | arrow : IsType A -> IsType B -> IsType (A → B)
  | farrow : IsType A -> IsType B -> IsType (A ⇒ B)
  | app : IsType A -> IsType B -> IsType (A `•k B)


theorem hs_type_neutral_form_is_type {τ h : HsTerm}:
  τ.IsType ->
  τ.neutral_form = .some (h, sp) ->
  h.IsType ∧ ∀ k ∈ sp, k.2.IsType := by
  intros h1 h2
  induction h1 generalizing h sp <;> simp at *
  case _ => cases h2; case _ h2 h3 =>
    cases h2; cases h3;
    constructor;constructor; simp
  case _ ih1 ih2 =>
    rw[Option.bind_eq_some] at h2; cases h2
    case _ h2 =>
    cases h2; case _ h2 h3 =>
    cases h3
    have ih1' := ih1 h2
    cases ih1'
    constructor; assumption
    intros; case _ h =>
    simp at h;
    cases h
    case _ ih a b h =>
      apply ih a b h
    case _ h =>
    cases h; case _ e1 e2 =>
    cases e1; cases e2
    assumption

theorem hs_is_type_neutral_form {τ : HsTerm} :
  τ.IsType ->
  τ.neutral_form = .some (`#τh, τs) ->
  (∀ τ ∈ τs, τ.fst = HsSpineVariant.kind ∧ τ.snd.IsType) := by
intro h1 h2
induction h1 generalizing τh τs <;> simp at h2
case _ =>
  cases h2; case _ h2a h2b =>
  cases h2a; cases h2b
  simp
case _ =>
  rw[Option.bind_eq_some] at h2;
  cases h2; case _ h2 =>
  cases h2; case _ h2 =>
  simp at h2
  cases h2; case _ ih _ w h1 h2a h2b =>
  have ih' := @ih τh w.snd (by simp_all; rw[<-h2a])
  rw[<-h2b]; simp; simp at ih'
  intros
  simp at *;
  constructor
  case _ h _ =>
    cases h;
    case _ h => replace ih' := ih' _ _ h; cases ih'; assumption
    case _ h => apply h.1
  case _ h _ =>
    cases h;
    case _ h => replace ih' := ih' _ _ h; cases ih'; assumption
    case _ h => cases h; case _ h => cases h; assumption




end HsTerm
