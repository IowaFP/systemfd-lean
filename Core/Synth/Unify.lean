import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

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
| _ => {}

def isNotAll : Core.Ty -> Bool
| ∀[_] _ => false
| .app t1 t2 | .arrow t1 t2 | .eq _ t1 t2 => isNotAll t1 ∧ isNotAll t2
| _ => true

-- There is a connection between Ty.FV and freeVars
theorem in_freeVars_iff_FV : ∀ x : Nat, T.isNotAll -> (x ∈ freeVars T <-> x ∈ T)
:= by
  intro x
  fun_induction freeVars
  intro h; simp; apply Iff.intro; intro h; subst h; apply FV.var; intro h; cases h; rfl
  case _ t1 t2 ih1 ih2 =>
    intro h1; simp [isNotAll] at h1; rcases h1 with ⟨h1, h2⟩
    · simp;
      replace ih1 := ih1 h1; replace ih2 := ih2 h2;
      apply Iff.intro
      intro h; cases h
      case _ h => rw[ih1] at h; apply FV.appr h
      case _ h => rw[ih2] at h; apply FV.appl h
      intro h; cases h
      case _ h => apply Or.inl; apply ih1.mpr h
      case _ h => apply Or.inr; apply ih2.mpr h
  case _ t1 t2 ih1 ih2 =>
    intro h1; simp [isNotAll] at h1; rcases h1 with ⟨h1, h2⟩
    · simp;
      replace ih1 := ih1 h1; replace ih2 := ih2 h2;
      apply Iff.intro
      intro h; cases h
      case _ h => rw[ih1] at h; apply FV.arrowr h
      case _ h => rw[ih2] at h; apply FV.arrowl h
      intro h; cases h
      case _ h => apply Or.inl; apply ih1.mpr h
      case _ h => apply Or.inr; apply ih2.mpr h
  case _ t1 t2 ih1 ih2 =>
    intro h1; simp [isNotAll] at h1; rcases h1 with ⟨h1, h2⟩
    · simp;
      replace ih1 := ih1 h1; replace ih2 := ih2 h2;
      apply Iff.intro
      intro h; cases h
      case _ h => rw[ih1] at h; apply FV.eqr h
      case _ h => rw[ih2] at h; apply FV.eql h
      intro h; cases h
      case _ h => apply Or.inl; apply ih1.mpr h
      case _ h => apply Or.inr; apply ih2.mpr h
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



-- There is a connection between Ty.FV and freeVars
theorem not_in_freeVars_iff_not_FV : ∀ x : Nat, T.isNotAll -> (x ∉ freeVars T <-> x ∉ T)
:= by
  intro x h; have lem := in_freeVars_iff_FV x h;
  contrapose; apply lem

@[simp]
def varsEqns : List (Ty × Ty) -> Finset Nat
| [] => {}
| .cons (t, u) eqs => freeVars t ∪ freeVars u ∪ varsEqns eqs

@[simp]
noncomputable def UnifyState.varsEqn : UnifyState -> Nat
| ⟨_, eqns⟩ => varsEqns eqns |> Finset.card


@[simp]
noncomputable def UnifyStateSize (u : UnifyState) : Nat × Nat := ⟨u.varsEqn, u.eqnSize⟩

def UnifyState.nonEmptyEqns : UnifyState -> Bool
| ⟨_, eqns⟩ => ¬ eqns.isEmpty

@[simp]
abbrev UResult (α : Type u) := Except (Ty × Ty) α

instance : Pure UResult where
  pure x := .ok x

-- Performs one step of "unification"
@[simp]
def unifyStep (u : UnifyState) (h : u.nonEmptyEqns) : UResult UnifyState :=
  match h1 : u.equations with
  | [] => by simp [UnifyState.nonEmptyEqns] at h; exfalso; apply h h1
  | .cons (t#x, t) eqs | .cons (t, t#x) eqs =>
    if (x ∉ freeVars t) ∧ t.isNotAll
    then let τ : Subst Ty := ⟨λ y => if x == y then .su t else .su t#y⟩
    return ⟨u.subst ∘ τ, eqs.map (λ (t, u) => (t[τ], u[τ]))⟩
    else .error (t#x, t)

  | .cons (gt#x, gt#y) eqs => if x == y then return ⟨u.subst, eqs⟩ else .error (gt#x, gt#y)
  | .cons (.arrow x1 y1, .arrow x2 y2) eqs
  | .cons (.app x1 y1, .app x2 y2) eqs =>
    return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩
  | .cons (.eq k1 x1 y1, .eq k2 x2 y2) eqs =>
    if k1 == k2 then return ⟨u.subst, (x1, x2) :: (y1, y2) :: eqs⟩ else .error (.eq k1 x1 y1, .eq k2 x2 y2)
  | .cons (t1, t2) tl => .error (t1, t2)


theorem loopUnifyDecreases {u u' : UnifyState} (invh : u.nonEmptyEqns) (h : unifyStep u invh = .ok u') :
  Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (UnifyStateSize u') (UnifyStateSize u)
:= by
  simp; rcases u with ⟨_, eqns⟩
  cases eqns
  case nil =>  simp [UnifyState.nonEmptyEqns] at invh
  case cons hd tl =>
  rcases hd with ⟨lhsTy, rhsTy⟩
  cases lhsTy
  all_goals (simp [unifyStep] at h)
  any_goals (clear invh)
  case var v =>
    split at h <;> try simp at h
    case _ h1 =>
    rcases h1 with ⟨h1, h2⟩; cases h
    simp; apply Prod.Lex.left;
    sorry

  case global =>
    cases rhsTy <;> try simp at h
    · split at h <;> try simp at h
      case _ h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
        generalize zdef : (insert v (varsEqns tl)).card = z at *
        simp [Finset.card_insert_eq_ite] at zdef
        split at zdef
        · subst zdef; sorry -- apply Prod.Lex.right; omega
        · subst zdef; apply Prod.Lex.left; sorry -- omega
    · split at h <;> try simp at h
      case _ e h => subst e; cases h; simp; apply Prod.Lex.right; omega

  case arrow =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      split at zdef
      · subst zdef; sorry -- apply Prod.Lex.right; omega
      · subst zdef; apply Prod.Lex.left; sorry -- omega
    case _ a1 a2 a3 a4 =>
      cases h; simp [size];
      have e : (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega

  case app =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      split at zdef
      · subst zdef; sorry -- apply Prod.Lex.right; omega
      · subst zdef; apply Prod.Lex.left; sorry -- omega
    case _ a1 a2 a3 a4 =>
      cases h; simp [size];
      have e : (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega


  case eq =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      split at zdef
      · subst zdef; sorry -- apply Prod.Lex.right; omega
      · subst zdef; apply Prod.Lex.left; sorry -- omega
    case _ a1 a2 _ a3 a4 =>
      split at h <;> try simp at h
      case _ e =>
        simp at e; subst e
        cases h; simp [size];
        have e : (a1.freeVars ∪ (a2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (a1.freeVars ∪ (a3.freeVars ∪ (a2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
        rw[e]; apply Prod.Lex.right; omega

  case all =>  cases rhsTy  <;> try simp [isNotAll] at h


def loopUnify (u : UnifyState) : UResult (Subst Core.Ty) :=
  if h : u.nonEmptyEqns
  then
    match h1 : unifyStep u h with
    | .ok u' => loopUnify u'
    | .error e => .error e
  else return u.subst
termination_by (UnifyStateSize u)
decreasing_by apply loopUnifyDecreases h h1


def EqnsUnifier (σ : Subst Core.Ty) : List (Core.Ty × Core.Ty) -> Prop
| .nil => True
| .cons (t, u) l => Unifier σ t u ∧ EqnsUnifier σ l


def UnifierOfSubst (σ σ' : Subst Ty) : Prop := ∀ (x : Nat), σ.inner x = (σ'.inner x)[σ]
def UnifierIdempotent (σ : Subst Ty) : Prop := UnifierOfSubst σ σ

def UnifierOfUnifyState (σ' : Subst Core.Ty) (u : UnifyState) : Prop :=
  UnifierOfSubst σ' u.subst ∧ EqnsUnifier σ' u.equations


theorem unifyStep_sound {u u': UnifyState} (h : u.nonEmptyEqns)(σ : Subst Core.Ty) :
  unifyStep u h = .ok u' -> UnifierOfUnifyState σ u' -> UnifierOfUnifyState σ u
:= by
  intro h1 h2
  unfold unifyStep at h1
  split at h1 <;> try simp at h1
  case _ e => simp [UnifyState.nonEmptyEqns] at h; exfalso; apply h e;
  case _ x t _ h3 =>
    split at h1 <;> try simp at h1
    case _ h4 =>
    rcases h4 with ⟨h4, h⟩
    cases h1; apply And.intro
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
    split at h1 <;> try simp at h1
    case _ h4 =>
    rcases h4 with ⟨h4, h⟩
    cases h1; apply And.intro
    · simp [UnifierOfSubst]; intro x'
      simp [UnifierOfUnifyState] at h2;
      rcases h2 with ⟨h1, h2⟩; simp [UnifierOfSubst] at h1;
      replace h1 := h1 x';
      -- The point here is that x ≠ x'. why?
      sorry
    · sorry

  case _ h3 =>
    split at h1 <;> try simp at h1
    case _ e =>
    subst e; cases h1
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    · apply h1
    · simp [h3, EqnsUnifier];
      apply And.intro
      · simp [Unifier]
      · apply h2
  case _ p1 =>
    cases h1
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind
  case _ p1 =>
    cases h1
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind
  case _ p1 =>
    split at h1 <;> try simp at h1
    case _ e =>
    cases h1; simp at e; subst e;
    simp [UnifierOfUnifyState] at *;
    rcases h2 with ⟨h1, h2⟩
    apply And.intro
    apply h1
    simp [p1, EqnsUnifier, Unifier] at *; grind


theorem unifyStep_idempotency {u u': UnifyState} (h : u.nonEmptyEqns) (hi : UnifierIdempotent u.subst) :
  unifyStep u h = .ok u' -> UnifierIdempotent u'.subst
:= by
  intro h
  unfold unifyStep at h
  split at h <;> try simp at h
  case _ e h1 =>
    simp [UnifyState.nonEmptyEqns] at e; exfalso; apply e h1
  case _ h3 =>
    split at h <;> try simp at h
    case _ h1 =>
    rcases h1 with ⟨h1, h2⟩
    cases h
    simp [UnifierIdempotent, UnifierOfSubst]; intro x'

    sorry
  sorry
  sorry
  sorry
  sorry
  sorry

theorem loopUnify_idempotency {σ  : Subst Ty} {u : UnifyState} (hi : UnifierIdempotent u.subst) (h : loopUnify u = .ok σ) : UnifierIdempotent σ
:= by
  unfold loopUnify at h;
  split at h
  case _ h1 =>
    generalize zdef : unifyStep u h1 = z at *
    cases z
    case error => simp at h
    case ok u' =>
    simp at h; replace hi := unifyStep_idempotency h1 hi zdef
    apply loopUnify_idempotency hi h
  case _ h1 => cases h; apply hi
termination_by (UnifyStateSize u)
decreasing_by case _ e _ _ => -- for some reason lean cannot figure this one out
  simp at h; apply loopUnifyDecreases e zdef


theorem loopUnify_sound {σ  : Subst Ty} {u : UnifyState} (hi : UnifierIdempotent u.subst) : loopUnify u = .ok σ -> UnifierOfUnifyState σ u
:= by
  intro h
  replace hi := loopUnify_idempotency hi h
  fun_induction loopUnify generalizing σ  <;> try simp at h
  case _ u' uss ih =>
    replace ih := ih h hi
    replace uss := unifyStep_sound _ σ uss
    apply uss ih
  case _  u h =>
    rcases u with ⟨us, ueqs⟩; cases h
    simp [UnifyState.nonEmptyEqns] at h; subst h; simp at *; simp [UnifierOfUnifyState]
    simp [UnifierIdempotent] at hi
    apply And.intro
    · apply hi
    · simp [EqnsUnifier]


def unify (t u : Core.Ty) : UResult (Subst Core.Ty) :=
  loopUnify ⟨Subst.id Core.Ty, [(t, u)]⟩

theorem Subst.id_idempotent : UnifierIdempotent (Subst.id Ty)
:= by
  simp [UnifierIdempotent, UnifierOfSubst]
  intro x; cases x <;> simp [Subst.id] at *


theorem unify_soundness {t u : Ty} {σ  : Subst Ty} : unify t u = .ok σ -> Unifier σ t u
:= by
  intro h
  unfold unify at h
  replace h := loopUnify_sound (Subst.id_idempotent) h
  simp [UnifierOfUnifyState] at h; rcases h with ⟨h1, h2⟩
  simp [EqnsUnifier] at h2; apply h2


theorem unify_completeness {t u : Ty} {σ  : Subst Ty} :
  Unifier σ t u -> unify t u = .ok σ'
  -> ∃ (τ : Subst Core.Ty), σ = σ' ∘ τ := by sorry


-- theorem unify_correctness : unify t u = some σ ↔ Unifier σ t u := ⟨unify_soundness, unify_completeness⟩

-- what about well kindedness?
-- we may want to have something like:
-- G,Δ ⊢ σ = ∀ i, ∃ k, G,Δ ⊢ (σ.act i).from_action : K
-- what is the theorems that we would like to write?
-- G&Δ ⊢ T : K ∧ G&Δ ⊢ σ -> G&Δ ⊢ T[σ] : K


end Core.Ty
