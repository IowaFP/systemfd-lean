import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Ctx

namespace Term

  inductive IsKind : Term -> Prop where
  | type : IsKind ★
  | arrow : IsKind A -> IsKind B -> IsKind (A -k> B)

  inductive IsType : Ctx Term  -> Term -> Prop where
  | var : Γ.is_datatype x || Γ.is_kind x -> IsType Γ #x
  | all : IsKind A -> IsType (.kind A :: Γ) B -> IsType Γ (∀[A] B)
  | arrow : IsType Γ A -> IsType (.empty :: Γ) B -> IsType Γ (A -t> B)
  | app : IsType Γ f -> IsType Γ a -> IsType Γ (f `@k a)
  | eq : IsKind K -> IsType Γ A -> IsType Γ B -> IsType Γ (A ~[K]~ B)

  theorem is_kind_disjoint_is_type : IsKind t -> ¬ IsType Γ t := by
  intro h1 h2
  induction h1
  all_goals (cases h2)

  theorem zero_not_is_kind : ¬ IsKind `0 := by intro h; cases h

  theorem zero_not_is_type : ¬ IsType Γ `0 := by intro h; cases h

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
  | #x => Γ.is_datatype x || Γ.is_kind x
  | (τ1 -t> τ2) => isType Γ τ1 && isType (.empty :: Γ) τ2
  | (∀[k]τ) => isKind k && isType (.kind k :: Γ) τ
  | τ1 `@k τ2 => isType Γ τ1 && isType  Γ τ2
  | τ1 ~[k]~ τ2 => isType Γ τ1 && isType  Γ τ2 && isKind k
  | _ => false

  def isTerm (Γ : Ctx Term) : Term -> Bool := λ t => not (isKind t || isType Γ t)


  theorem is_kind_shape_sound : isKind t -> IsKind t := by
    intro j; induction t using isKind.induct <;> unfold isKind at j
    case _ => constructor
    case _ ih1 ih2 =>
      simp at j;
      replace ih1 := ih1 j.1
      replace ih2 := ih2 j.2
      constructor; assumption; assumption
    case _ => simp at j

  theorem is_type_shape_sound : isType Γ t -> IsType Γ t := by
    intro j; induction Γ, t using isType.induct <;> unfold isType at j
    case _ => constructor; assumption
    case _ ih1 ih2 =>
      simp at j;
      replace ih1 := ih1 j.1
      replace ih2 := ih2 j.2
      constructor; assumption; assumption
    case _ ih =>
      simp at j
      replace ih := ih j.2
      have lem := is_kind_shape_sound j.1
      constructor; assumption; assumption
    case _ ih1 ih2 =>
      simp at j;
      replace ih1 := ih1 j.1
      replace ih2 := ih2 j.2
      constructor; assumption; assumption
    case _ ih1 ih2 =>
      simp at j
      replace ih1 := ih1 j.1.1
      replace ih2 := ih2 j.1.2
      have lem := is_kind_shape_sound j.2
      constructor; assumption; assumption; assumption
    case _ ih1 ih2 =>
      simp at j

theorem mk_kind_app_rev_is_type {h : Term} {args : List Term} :
  (h.IsType Γ ∧
  ∀ a ∈ args, a.IsType Γ) ->
  (mk_kind_app_rev h args).IsType Γ := by
  intro j1
  cases j1; case _ j1 j2 =>
  induction args <;> simp at *
  case _ => assumption
  case _ hd tl ih =>
  cases j2; case _ j2 j3 =>
  replace ih := ih j3
  constructor; assumption; assumption

theorem arrow_kind_split_is_type (k : Term) :
  k.IsType Γ ->
  Term.split_kind_arrow k = .some (κs, base_κ) ->
  (base_κ.IsType Γ ∧ ∀ k ∈ κs, k.IsType Γ) := by
 intros; induction k generalizing κs base_κ <;> simp at *
 case _ h1 h2 =>
   cases h2; case _ h2 h3 =>
   cases h3
   constructor; assumption; rw[h2]; simp
 case _ v _ _ ih1 ih2 h1 h2 =>
   cases v <;> simp at *
   cases h1
end Term
