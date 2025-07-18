import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Ctx

namespace Term

  inductive IsKind : Term -> Prop where
  | type : IsKind ★
  | arrow : IsKind A -> IsKind B -> IsKind (A -k> B)

  inductive IsType : Term -> Prop where
  | var : IsType #x
  | all : IsKind A -> IsType B -> IsType (∀[A] B)
  | arrow : IsType A -> IsType B -> IsType (A -t> B)
  | app : IsType A -> IsType B -> IsType (f `@k a)
  | eq : IsKind K -> IsType A -> IsType B -> IsType (A ~[K]~ B)

  theorem is_kind_disjoint_is_type : IsKind t -> ¬ IsType t := by
  intro h1 h2
  induction h1
  all_goals (cases h2)

  theorem zero_not_is_kind : ¬ IsKind `0 := by intro h; cases h

  theorem zero_not_is_type : ¬ IsType `0 := by intro h; cases h

  theorem is_kind_from_subst : IsKind ([σ]t) -> IsKind t ∨ (∃ i, ∃ v, σ i = .su v ∧ IsKind v) := by
  intro h; induction t generalizing σ
  all_goals simp at h; try cases h
  case var x =>
    generalize zdef : σ x = z at *
    cases z <;> simp at *; cases h
    case _ v =>
      apply Or.inr; apply Exists.intro x
      apply Exists.intro v
      apply And.intro zdef h
  case type => apply Or.inl; constructor
  case arrow ih1 ih2 h1 h2 =>
    replace ih1 := ih1 h1
    replace ih2 := ih2 h2
    cases ih1
    case _ ih1 =>
      cases ih2
      case _ ih2 =>
        apply Or.inl; constructor
        assumption; assumption
      case _ ih2 => apply Or.inr ih2
    case _ ih1 => apply Or.inr ih1

  theorem is_kind_from_beta : IsKind (b β[t]) -> IsKind t ∨ IsKind b := by
  intro h
  have lem := is_kind_from_subst h
  cases lem; case _ lem => apply Or.inr lem
  case _ lem =>
  cases lem; case _ i lem =>
  cases lem; case _ v lem =>
  cases lem; case _ lem1 lem2 =>
  cases i <;> simp at lem1
  case _ => subst lem1; apply Or.inl lem2

  theorem constant_non_variables_preserved_under_substitution σ :
    t.size = 0 -> (∀ n, t ≠ #n) -> ([σ]t) = t
  := by
  intro h1 h2; induction t generalizing σ
  all_goals simp
  all_goals try solve | cases h1
  case _ i =>
    generalize zdef : σ i = z at *
    cases z <;> simp at *


  def isKind : Term -> Bool
  | ★ => true
  | k1 -k> k2 => isKind k1 && isKind k2
  | _ => false


  def isType (Γ : Ctx Term) : Term -> Bool
  | #x => Γ.is_datatype x || Γ.is_type x
  | (τ1 -t> τ2) => isType Γ τ1 && isType (.type τ1 :: Γ) τ2
  | τ1 `@k τ2 => isType Γ τ1 && isType  Γ τ2
  | _ => false

  def isTerm (Γ : Ctx Term) : Term -> Bool := λ t => not (isKind t || isType Γ t)

end Term
