import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Functor
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import Core.Ty.Definition
import Core.Ty.Substitution
import Core.Ty.Structure

import Core.Typing

import LeanSubst
import Lilac

open LeanSubst

namespace LeanSubst

def Subst.Dom (σ : Subst Core.Ty) := ∀ i, Core.Ty.from_action (σ.act i) ≠ t#i

end LeanSubst

namespace Core.Ty

/-- heavily inspired by https://github.com/codyroux/traat-lean/tree/main/Traat -/

-- σ is a unifier for t and u if t[σ] = u[σ]
def Unifier (σ : Subst Ty) (t u : Core.Ty) : Prop := t[σ] = u[σ]


-- def Unify (t u : Core.Ty) := ∃ σ : Subst Ty, t[σ] = u[σ]

-- what about most general unifier?

--
-- Proving termination for this is going to be very annoying
partial def unify' : (t u : Ty) -> Option (Subst Ty)
| .var x, t => return ⟨λ y => if x == y then su t else su t#x⟩
| .global x, .global y => if x == y then return Subst.id Ty else none
| .arrow x1 y1, .arrow x2 y2 | .app x1 y1, .app x2 y2 => do
  let σ1 <- unify' x1 y1
  let σ2 <- unify' x2 y2
  return σ1 ∘ σ2
| .eq k1 x1 y1, .eq k2 x2 y2 =>
  if k1 == k2 then do
  let σ1 <- unify' x1 y1
  let σ2 <- unify' x2 y2
  return σ1 ∘ σ2
  else none
| _, _ => none


/-- Contains 2 things, the unprocessed equalties, and the coercion itself -/
structure UnifyState where
  subst : Subst Core.Ty
  equations : List (Ty × Ty)

-- def UnifyState.id : UnifyState := ⟨Subst.id Ty, []⟩

@[simp]
noncomputable def eqnsSize : List (Ty × Ty) -> Nat
| [] => 0
| .cons (t1, t2) eqns => 1 + t1.size + t2.size + eqnsSize eqns

@[simp]
noncomputable def UnifyState.eqnSize : UnifyState -> Nat
| ⟨_, eqns⟩ => eqnsSize eqns

@[simp]
noncomputable def isVar : Core.Ty -> Bool
| t#_ => true
| _ => false

@[simp]
noncomputable def flipEqnsSize : List (Ty × Ty) -> Nat
| [] => 0
| .cons (t1, t2) es => if (¬ isVar t1) ∧ isVar t2 then 1 + flipEqnsSize es else flipEqnsSize es

@[simp]
noncomputable def UnifyState.flippedEqnSize : UnifyState -> Nat
| ⟨_, eqns⟩ => flipEqnsSize eqns

-- There is a triple we need to define as a termination measure
-- According to TRAAT
-- n1 = number of variables that are not in solved form
-- n2 = size of S i.e. eqnSize above
-- n3 = number of equations of the form (t = x) in S

-- however in this implementation, (t = x) ant (x = t) are treated as "solved" form
-- so we do not need n3 as our termination measure.
-- This might bite me somewhere else while proving things, or may be not,
-- we well see...


@[simp]
def freeVars : Core.Ty -> Finset Nat
| t#x => {x}
| .app t1 t2 | .arrow t1 t2 | .eq _ t1 t2 => freeVars t1 ∪ freeVars t2
-- | ∀[_] T =>
--   let fv : Finset Nat := freeVars T
--   let ze : Finset Nat := {0}
--   fv \ ze
| _ => {}

def isNotAll : Core.Ty -> Bool
| ∀[_] _ => false
| .app t1 t2 => isNotAll t1 ∧ isNotAll t2
| _ => true

-- There is a connection between Ty.FV and freeVars
theorem in_freeVars_iff_FV : ∀ x : Nat, T.isNotAll -> (x ∈ freeVars T <-> x ∈ T)
:= by
  intro x
  fun_induction freeVars
  intro h; simp; apply Iff.intro; intro h; subst h; apply FV.var; intro h; cases h; rfl
  case _ t1 t2 ih1 ih2 =>
    intro h1; simp [isNotAll] at h1; rcases h1 with ⟨h1, h2⟩
    · simp; sorry

  sorry
  sorry
  case _ t h1 h2 h3 h4 =>
  intro h
  cases t;
  case _ y => exfalso; apply h1 y rfl
  case _ y =>
    apply Iff.intro
    intro h1; cases h1
    intro h; cases h
  case _ t1 t2 => exfalso; apply h3 t1 t2 rfl
  case _ k t1 => simp [isNotAll] at h
  case _ t1 t2 => exfalso; apply h2 t1 t2 rfl
  case _ k t1 t2 => exfalso; apply h4 k t1 t2 rfl


@[simp]
def varsEqns : List (Ty × Ty) -> Finset Nat
| [] => {}
| .cons (t, u) eqs => freeVars t ∪ freeVars u ∪ varsEqns eqs

@[simp]
noncomputable def UnifyState.varsEqn : UnifyState -> Nat
| ⟨_, eqns⟩ => varsEqns eqns |> Finset.card


@[simp]
noncomputable def UnifyStateSize (u : UnifyState) : Nat × Nat := ⟨u.varsEqn, u.eqnSize⟩

-- TODO: use UResult instead of Option
def UResult (α : Type u) := Except (Ty × Ty) α
-- Problem, what should unifyStep return in case of empty equations?

-- Performs one step of "unification"
@[simp]
def unifyStep (u : UnifyState) : Option UnifyState :=
  match u.equations with
  | [] => none
  | .cons (t#x, t) eqs =>
    --- if (x ∉ freeVars t)
    -- then
    let τ : Subst Ty := ⟨λ y => if x == y then .su t else .su t#y⟩
    return ⟨u.subst ∘ τ, eqs.map (λ (t, u) => (t[τ], u[τ]))⟩
    -- else none
  | .cons (t, t#x) eqs =>
    let τ : Subst Ty := ⟨λ y => if x == y then .su t else .su t#y⟩
    return ⟨u.subst ∘ τ, eqs⟩
  | .cons (gt#x, gt#y) eqs => if x == y then return ⟨u.subst, eqs⟩ else none
  | .cons (.arrow x1 y1, .arrow x2 y2) eqs
  | .cons (.app x1 y1, .app x2 y2) eqs =>
    return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩
  | .cons (.eq k1 x1 y1, .eq k2 x2 y2) eqs =>
    if k1 == k2 then return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩ else none
  | _ => none


theorem loopUnifyDecreases {u u' : UnifyState} (h : unifyStep u = some u') :
  Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (UnifyStateSize u') (UnifyStateSize u)
:= by
  simp; cases u
  case _ eqns =>
  cases eqns
  case nil => simp [unifyStep] at h
  case cons hd tl =>
  rcases hd with ⟨lhsTy, rhsTy⟩
  cases lhsTy
  all_goals (simp [unifyStep] at h)
  all_goals try (subst u'; simp)

  case var v =>
    generalize z1def : rhsTy.freeVars ∪ varsEqns tl = z1 at *
    generalize zdef : (insert v z1) = z at *
    have lem1 : z.card ≤ (z1.card + 1) := by simp [<-zdef]; apply Finset.card_insert_le
    have lem2 := Finset.card_union_le rhsTy.freeVars (varsEqns tl)
    rw[<-zdef, <-z1def] at lem1
    cases Nat.decEq (varsEqns tl).card (insert v (rhsTy.freeVars ∪ varsEqns tl)).card
    case _ h =>

      sorry
    case _ h => sorry -- rw[h]; apply Prod.Lex.right; omega
  · cases rhsTy <;> try simp at h
    · subst u'; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      split at zdef
      · subst zdef; apply Prod.Lex.right; omega
      · subst zdef; apply Prod.Lex.left; omega
    · rcases h with ⟨e1, e2⟩; subst e1 e2; simp; apply Prod.Lex.right; omega
  · cases rhsTy <;> try simp at h
    · subst u'; simp; sorry
    · subst u'; simp [Ty.size]; case _ a1 a2 a3 a4 =>
      have e : (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                            (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega
  · cases rhsTy <;> try simp at h
    subst u'; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      split at zdef
      · subst zdef; apply Prod.Lex.right; omega
      · subst zdef; apply Prod.Lex.left; omega
  · cases rhsTy <;> try simp at h
    all_goals (subst u'; simp)
    · sorry
    case _ a1 a2 a3 a4 =>
    have e : (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                          (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
    rw[e]; apply Prod.Lex.right; simp [Ty.size]; omega
  · cases rhsTy <;> try simp at h
    · subst u'; simp [Ty.size];
      case _ t1 t2 v =>
      generalize zdef : t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl) = z at *
      generalize z1def : (t2.freeVars ∪ varsEqns tl) = z1 at *
      have lem : (varsEqns tl).card ≤ z1.card := by simp [<-z1def]; sorry
      sorry
    · rcases h with ⟨e1, e2⟩; subst e1 e2; simp;
      simp [Ty.size];
      case _ a1 a2 a3 a4 =>
      have e : (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                            (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega


def loopUnify (u : UnifyState) : Option (Subst Core.Ty)
:= match h : (unifyStep u) with
  | none => none
  | some ⟨σ, []⟩ => return σ
  | some u' => loopUnify u'
termination_by (UnifyStateSize u)
decreasing_by (apply loopUnifyDecreases h)


def EqnsUnifier (σ : Subst Core.Ty) : List (Core.Ty × Core.Ty) -> Prop
| .nil => True
| .cons (t, u) l => Unifier σ t u ∧ EqnsUnifier σ l


def UnifierOfSubst (σ σ' : Subst Ty) : Prop := ∀ (x : Nat), σ.inner x = (σ'.inner x)[σ]
def UnifierIdempotent (σ : Subst Ty) : Prop := UnifierOfSubst σ σ

def UnifierOfUnifyState (σ' : Subst Core.Ty) (u : UnifyState) : Prop :=
  UnifierOfSubst σ' u.subst ∧ EqnsUnifier σ' u.equations


theorem unifyStep_sound {u : UnifyState} (σ : Subst Core.Ty): unifyStep u = some u' -> UnifierOfUnifyState σ u' -> UnifierOfUnifyState σ u
:= by
  intro h1 h2
  unfold unifyStep at h1
  split at h1 <;> simp at *
  case _ x t _ h3 =>
    subst u'; apply And.intro
    · simp [UnifierOfSubst]; intro x'
      simp [UnifierOfUnifyState] at h2;
      rcases h2 with ⟨h1, h2⟩; simp [UnifierOfSubst] at h1;
      replace h1 := h1 x';
      -- The point here is that x ≠ x'. why?
      sorry
    · simp [h3, EqnsUnifier];
      simp [UnifierOfUnifyState] at h2
      rcases h2 with ⟨h1, h2⟩
      apply And.intro
      · simp [UnifierOfSubst] at h1; simp [Unifier];
        replace h1 := h1 x; simp [Subst.act, SubstAction.act]; rw[h1];
        -- The point here is that u.subst does not have x in its domain
        -- hence lhs and rhs of the goal are the same
        -- Why does u.subst does not have x in its domain?
        -- becuase if it did, then (x, t) would not appear here, it would have been replaced by t'
        sorry
      · sorry -- apply h2


  case _ p1 p2 =>
    -- this case is very similar to the above case, just that its (t, x) instead of (x, t)
    subst h1;
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    simp [UnifierOfSubst] at *; intro x; replace h1 := h1 x;
    sorry
    simp [p1, EqnsUnifier]; apply And.intro;
    sorry;
    apply h2
  case _ h3 =>
    rcases h1 with ⟨e1, e2⟩; subst e1 e2;
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    · apply h1
    · simp [h3, EqnsUnifier];
      apply And.intro
      · simp [Unifier]
      · apply h2
  case _ p1 =>
    subst u'
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind
  case _ p1 =>
    subst u'
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind
  case _ p1 =>
    rcases h1 with ⟨e, h1⟩; subst e;
    subst u'
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind


theorem unifyStep_idempotency {u : UnifyState} (hi : UnifierIdempotent u.subst) : unifyStep u = some u' -> UnifierIdempotent u'.subst
:= by
  intro h
  unfold unifyStep at h
  split at h <;> simp at h
  case _ h3 =>
    subst u'
    simp [UnifierIdempotent, UnifierOfSubst]; intro x'

    sorry
  sorry
  sorry
  sorry
  sorry
  sorry

theorem loopUnify_idempotency {σ  : Subst Ty} {u : UnifyState} (hi : UnifierIdempotent u.subst) (h : loopUnify u = some σ) : UnifierIdempotent σ
:= by
  unfold loopUnify at h;
  generalize zdef : unifyStep u = z at *
  cases z
  case none => simp at h
  case some u' =>
  replace hi := unifyStep_idempotency hi zdef
  split at h <;> simp at *
  subst u'; subst h; simp at hi; apply hi
  subst u'; apply loopUnify_idempotency hi h
termination_by (UnifyStateSize u)
decreasing_by case _ h1 _ _ _ _ e _ _ =>  cases e; apply loopUnifyDecreases h1 -- for some reason lean couldn't figure this out



theorem loopUnify_sound {σ  : Subst Ty} {u : UnifyState} (hi : UnifierIdempotent u.subst) : loopUnify u = some σ -> UnifierOfUnifyState σ u
:= by
  intro h
  replace hi := loopUnify_idempotency hi h
  fun_induction loopUnify generalizing σ <;> try simp at h
  case _ u σ h1 =>
    subst h; unfold UnifierOfUnifyState; rcases u with ⟨s, eqs⟩;
    replace h1 := unifyStep_sound σ h1
    simp;
    have lem : UnifierOfUnifyState σ { subst := σ, equations := [] } := by
      unfold UnifierOfUnifyState; simp [EqnsUnifier];
      apply hi
    replace h1 := h1 lem;
    unfold UnifierOfUnifyState at h1; simp at h1; apply h1
  case _ ih => replace ih := ih h hi; apply unifyStep_sound σ; assumption; apply ih


def unify (t u : Core.Ty) : Option (Subst Core.Ty) :=
  loopUnify ⟨Subst.id Core.Ty, [(t, u)]⟩

theorem Subst.id_idempotent : UnifierIdempotent (Subst.id Ty)
:= by
  simp [UnifierIdempotent, UnifierOfSubst]
  intro x; cases x <;> simp [Subst.id] at *


theorem unify_soundness {t u : Ty} {σ  : Subst Ty} : unify t u = some σ -> Unifier σ t u
:= by
  intro h
  unfold unify at h
  replace h := loopUnify_sound (Subst.id_idempotent) h
  simp [UnifierOfUnifyState] at h; rcases h with ⟨h1, h2⟩
  simp [EqnsUnifier] at h2; apply h2


theorem unify_completeness {t u : Ty} {σ  : Subst Ty} :
  Unifier σ t u -> unify t u = some σ'
  -> ∃ (τ : Subst Core.Ty), σ = σ' ∘ τ := by sorry


-- theorem unify_correctness : unify t u = some σ ↔ Unifier σ t u := ⟨unify_soundness, unify_completeness⟩

-- what about well kindedness?
-- we may want to have something like:
-- G,Δ ⊢ σ = ∀ i, ∃ k, G,Δ ⊢ (σ.act i).from_action : K
--


end Core.Ty
