import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
def Unifier (σ : Subst Ty) (t u : Ty) : Prop := t[σ] = u[σ]


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


/-- Contains 2 things, the unprocessed equalties, and the coercion itself (normal forms from TRAAT) -/
structure UnifyState where
  subst : Subst Ty
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
noncomputable def isVar : Ty -> Bool
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
def freeVars : Ty -> Finset Nat
| t#x => {x}
| .app t1 t2 | .arrow t1 t2 | .eq _ t1 t2 => freeVars t1 ∪ freeVars t2
| _ => {}

def isNotAll : Ty -> Bool
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

-- We only consider those UnifyState that does not have foralls in it
def UnifyStateWf (u : UnifyState) : Bool := u.equations.all (λ t => t.1.isNotAll ∧ t.2.isNotAll)

-- Performs one step of "unification"
@[simp]
def unifyStep (u : UnifyState) (h : u.nonEmptyEqns ∧ UnifyStateWf u) : UResult UnifyState :=
  match h1 : u.equations with
  | [] => by simp [UnifyState.nonEmptyEqns] at h; exfalso; apply h.1 h1
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

@[simp, grind =]
def unifyFails : Ty -> Ty -> Bool
| t#_, _
| _, t#_
| gt#_, gt#_
| _ -:> _, _ -:> _
| .app _ _, .app _ _ => false
| .eq k1 _ _, .eq k2 _ _ => k1 != k2
| _ , _ => true


theorem eqns_ind {motive : List (Ty × Ty) -> Prop} (l : List (Ty × Ty))
  (h1   :                                motive [])
  (h2   : ∀ l x t,           motive l -> motive ((t#x, t)::l))
  (h3   : ∀ l x t,           (∀ y, t ≠ t#y) -> motive l -> motive ((t, t#x)::l))
  (h4   : ∀ l x y,           motive l -> motive ((gt#x, gt#y) :: l))
  (h5   : ∀ l t1 u1 t2 u2,   motive l -> motive (((t1 -:> u1), (t2 -:> u2)) :: l))
  (h6   : ∀ l t1 u1 t2 u2,   motive l -> motive (((.app t1 u1), (.app t2 u2)) :: l))
  (h7   : ∀ l k t1 u1 t2 u2, motive l -> motive (((.eq k t1 u1), (.eq k t2 u2)) :: l))
  (dflt : ∀ l t u,           unifyFails t u -> motive ((t, u) :: l))
  : motive l
:= by
  induction l
  case nil => apply h1
  case cons x xs ih =>
  rcases x with ⟨t, u⟩
  cases t <;> cases u <;> try grind
  case _ k1 t1 u1 k2 t2 u2 =>
  if h : k1 = k2
  then subst h; apply h7 xs; apply ih
  else apply dflt; simp; apply h

theorem var_not_free_after_subst {t s : Ty} {x : Nat} {σ : Subst Ty}
  (h2 : x ∉ s)
  (h3 : t.isNotAll) (h4 : s.isNotAll):
  σ = ⟨λ y => if x == y then .su s else .su t#y⟩ ->
  x ∉ freeVars (t[σ]) -- = freeVars s ∪ freeVars t -- - { x }
:= by
  intro e
  subst e; simp;
  match t with
  | .var z =>
    simp; have lem := not_in_freeVars_iff_not_FV x h4;
    cases decEq x z
    case _ =>
      have e : (x = z) = False := by grind
      simp [e]
    case _ e => subst e; simp; simp [lem]; apply h2
  | .global _ => simp
  | .arrow t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp; apply And.intro
    · simp [var_not_free_after_subst h2 h3a h4]
    · simp [var_not_free_after_subst h2 h3b h4]
  | .app t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp; apply And.intro
    · simp [var_not_free_after_subst h2 h3a h4]
    · simp [var_not_free_after_subst h2 h3b h4]
  | .eq k t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp; apply And.intro
    · simp [var_not_free_after_subst h2 h3a h4]
    · simp [var_not_free_after_subst h2 h3b h4]
  | .all k t => simp [Ty.isNotAll] at h3

theorem var_not_free_after_subst_on_eqns {eqns : List (Ty × Ty)} {s : Ty} {x : Nat} {σ : Subst Ty}
  (h2 : x ∉ s)
  (h3 : ∀ t ∈ eqns, t.1.isNotAll ∧ t.2.isNotAll) (h4 : s.isNotAll):
  σ = ⟨λ y => if x == y then .su s else .su t#y⟩ ->
  x ∉ varsEqns (eqns.map (λ (t1, t2) => (t1[σ], t2[σ])))
:= by
  intro e; subst e; simp
  match eqns with
  | .nil => simp
  | .cons ⟨t1, t2⟩ eqns =>
    have h3 := h3 (t1, t2) (by constructor); rcases h3 with ⟨h1a, h2a⟩; simp at h1a h2a
    simp [varsEqns];
    apply And.intro
    · apply var_not_free_after_subst h2 h1a h4; simp
    · apply And.intro
      · apply var_not_free_after_subst h2 h2a h4; simp
      · have lem : ∀ t ∈ eqns, t.1.isNotAll ∧ t.2.isNotAll := by grind
        simp [var_not_free_after_subst_on_eqns h2 lem h4]

-- TODO : How do we describe subtraction on finsets?
theorem freevars_after_subst {t s : Ty} {σ : Subst Ty}
  (h2 : x ∉ s)
  (h3 : t.isNotAll) (h4 : s.isNotAll):
  σ = ⟨λ y => if x == y then .su s else .su t#y⟩ ->
  freeVars (t[σ]) ⊆ ((freeVars s ∪ freeVars t) \ {x})
:= by
  intro σdef;
  match t with
  | .var z =>
    simp; have lem := not_in_freeVars_iff_not_FV x h4;
    cases decEq x z
    case _ =>
      have e : (x = z) = False := by grind
      simp [e, σdef]; grind
    case _ e => subst e; simp [σdef]; grind
  | .global _ => simp
  | .arrow t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp;
    have lem1 := freevars_after_subst h2 h3a h4 σdef
    have lem2 := freevars_after_subst h2 h3b h4 σdef
    grind
  | .app t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp;
    have lem1 := freevars_after_subst h2 h3a h4 σdef
    have lem2 := freevars_after_subst h2 h3b h4 σdef
    grind
  | .eq k t1 t2 =>
    simp [isNotAll] at h3; rcases h3 with ⟨h3a, h3b⟩
    simp;
    have lem1 := freevars_after_subst h2 h3a h4 σdef
    have lem2 := freevars_after_subst h2 h3b h4 σdef
    grind
  | .all k t => simp [Ty.isNotAll] at h3

theorem freevars_after_subst_on_eqns {s : Ty} {σ : Subst Ty} {eqns : List (Ty × Ty)}
  (h2 : x ∉ s)
  (h3 : ∀ t ∈ eqns, t.1.isNotAll ∧ t.2.isNotAll) (h4 : s.isNotAll):
  σ = ⟨λ y => if x == y then .su s else .su t#y⟩ ->
  varsEqns (eqns.map (λ (t1, t2)=> (t1[σ], t2[σ]))) ⊆ s.freeVars ∪ varsEqns eqns \ {x}
:= by
  intro σdef
  simp; fun_induction varsEqns
  simp
  case _ t1 t2 eqns ih =>
    simp;
    replace ih1 := ih (by intro t h; apply h3; constructor; apply h)
    replace h3 := h3 ⟨t1, t2⟩ (by constructor); simp at h3
    have lem1 := freevars_after_subst h2 h3.1 (σ := σ) h4 (by simp [σdef])
    have lem2 := freevars_after_subst h2 h3.2 (σ := σ) h4 (by simp [σdef])
    grind

theorem loopUnifyDecreases {u u' : UnifyState} (invh : u.nonEmptyEqns ∧ UnifyStateWf u) (h : unifyStep u invh = .ok u') :
  Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (UnifyStateSize u') (UnifyStateSize u)
:= by
  simp; rcases u with ⟨_, eqns⟩
  cases eqns
  case nil =>  simp [UnifyState.nonEmptyEqns] at invh
  case cons hd tl =>
  rcases hd with ⟨lhsTy, rhsTy⟩
  cases lhsTy
  all_goals (simp [unifyStep] at h)
  -- any_goals (clear invh)
  case var v =>
    split at h <;> try simp at h
    case _ h1 =>
    rcases h1 with ⟨h1, h2⟩; cases h
    simp;
    simp [not_in_freeVars_iff_not_FV v h2] at h1
    let σ : Subst Ty := ⟨λ y => if v = y then su rhsTy else su t#y⟩
    have wf : ∀ t ∈ tl, t.1.isNotAll ∧ t.2.isNotAll := by
      intro t h; simp [UnifyStateWf] at invh; apply invh.2.2 t.1 t.2 h
    have lem := var_not_free_after_subst_on_eqns (eqns := tl) h1 (σ := σ)
    simp at lem;
    replace lem := lem (by intro t1 t2 h; apply wf ⟨t1, t2⟩ h) h2 (by simp [σ])
    have lem2 := freevars_after_subst_on_eqns (eqns := tl) h1 (σ := σ) wf h2 (by simp [σ])
    simp [σ] at lem2;
    -- have lem3 : rhsTy.freeVars ∪ varsEqns tl ⊆ insert v (rhsTy.freeVars ∪ varsEqns tl) := by grind
    cases Finset.decidableMem v (varsEqns tl)
    case _ d =>
      apply Prod.Lex.left
      have lem4a : v ∉ rhsTy.freeVars ∪ varsEqns tl := by
        intro h; simp at h; cases h;
        case _ h => apply h1; simp [in_freeVars_iff_FV v h2] at h; apply h
        case _ h => apply d; apply h

      have lem5 : rhsTy.freeVars ∪ varsEqns tl \ {v} = rhsTy.freeVars ∪ varsEqns tl := by grind

      have lem6 : (rhsTy.freeVars ∪ varsEqns tl).card < (insert v (rhsTy.freeVars ∪ varsEqns tl)).card := by grind
      rw[lem5] at lem2;
      have lem8 : varsEqns (tl.map (λ t => (t.1[σ], t.2[σ]))) ⊆ rhsTy.freeVars ∪ varsEqns tl := by grind
      have lem9 : (varsEqns (tl.map (λ t => (t.1[σ], t.2[σ])))).card ≤ (rhsTy.freeVars ∪ varsEqns tl).card := by
        apply Finset.card_le_card lem8
      simp [σ] at *
      grind
    case _ d =>
      have lem4a : v ∈ rhsTy.freeVars ∪ varsEqns tl := by grind
      have lem3 : rhsTy.freeVars ∪ varsEqns tl = insert v (rhsTy.freeVars ∪ varsEqns tl) := by grind
      apply Prod.Lex.left
      have lem8 : varsEqns (tl.map (λ t => (t.1[σ], t.2[σ]))) < rhsTy.freeVars ∪ varsEqns tl := by grind
      have lem9 : (varsEqns (tl.map (λ t => (t.1[σ], t.2[σ])))).card < (rhsTy.freeVars ∪ varsEqns tl).card := by apply Finset.card_lt_card lem8
      rw[<-lem3]; omega

  case global s =>
    cases rhsTy <;> try simp at h
    · split at h <;> try simp at h
      case _ h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
        generalize zdef : (insert v (varsEqns tl)).card = z at *
        simp [Finset.card_insert_eq_ite] at zdef
        let σ : Subst Ty := ⟨λ y => if v = y then su gt#s else su t#y⟩
        have lem := var_not_free_after_subst_on_eqns (eqns := tl) (s := gt#s) (x := v) (σ := σ) (by intro h; cases h) (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind) (by simp [isNotAll]) (by simp [σ])
        have lem2 := freevars_after_subst_on_eqns (eqns := tl) (s := gt#s) (x := v) (σ := σ) (by intro h; cases h) (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind) (by simp [isNotAll]) (by simp [σ])
        simp at lem2 lem;
        split at zdef <;> subst zdef
        case _ d =>
          apply Prod.Lex.left;
          have lem3 : (varsEqns tl \ {v}) < varsEqns tl := by grind
          have lem4 : (varsEqns tl \ {v}).card < (varsEqns tl).card := by grind
          have lem5 : (varsEqns (List.map (fun x => (x.1[σ], x.2[σ])) tl)).card ≤ (varsEqns tl \ {v}).card := by
            apply Finset.card_le_card lem2
          grind
        case _ d =>
          apply Prod.Lex.left;
          have lem3 : varsEqns tl \ {v} ⊆ varsEqns tl := by grind
          have lem4 : varsEqns (List.map (fun x => (x.1[σ], x.2[σ])) tl) ⊆ varsEqns tl := by grind
          have lem5 : (varsEqns (List.map (fun x => (x.1[σ], x.2[σ])) tl)).card ≤ (varsEqns tl).card := by apply Finset.card_le_card lem4
          grind
    · split at h <;> try simp at h
      case _ e h => subst e; cases h; simp; apply Prod.Lex.right; omega

  case arrow t1 t2 =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ v h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      let σ : Subst Ty := ⟨λ y => if v = y then su (t1 -:> t2) else su t#y⟩
      simp [isNotAll] at h2
      have h1' := h1
      simp [not_in_freeVars_iff_not_FV v h2.1] at h1
      simp [not_in_freeVars_iff_not_FV v h2.2] at h1
      have lem := var_not_free_after_subst_on_eqns
                   (eqns := tl) (s := (t1 -:> t2)) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      have lem2 := freevars_after_subst_on_eqns
                   (eqns := tl) (s := (t1 -:> t2)) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      simp at lem2 lem;
      split at zdef <;> subst zdef
      case _ d =>
        have lem5 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v}))  < (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind

        apply Prod.Lex.left;
        replace lem6 := Finset.card_lt_card lem6
        grind;
      case _ d =>
        apply Prod.Lex.left;
        replace lem2 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v})) = (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind
        grind
    case _ a3 a4 =>
      cases h; simp [size];
      have e : (t1.freeVars ∪ (t2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (t1.freeVars ∪ (a3.freeVars ∪ (t2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega

  case app t1 t2 =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ v h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      let σ : Subst Ty := ⟨λ y => if v = y then su (.app t1 t2) else su t#y⟩
      simp [isNotAll] at h2
      have h1' := h1
      simp [not_in_freeVars_iff_not_FV v h2.1] at h1
      simp [not_in_freeVars_iff_not_FV v h2.2] at h1
      have lem := var_not_free_after_subst_on_eqns
                   (eqns := tl) (s := (.app t1 t2)) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      have lem2 := freevars_after_subst_on_eqns
                   (eqns := tl) (s := (.app t1 t2)) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      simp at lem2 lem;
      split at zdef <;> subst zdef
      case _ d =>
        have lem5 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v}))  < (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind

        apply Prod.Lex.left;
        replace lem6 := Finset.card_lt_card lem6
        grind;
      case _ d =>
        apply Prod.Lex.left;
        replace lem2 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v})) = (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind
        grind
    case _ a3 a4 =>
      cases h; simp [size];
      have e : (t1.freeVars ∪ (t2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (t1.freeVars ∪ (a3.freeVars ∪ (t2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
      rw[e]; apply Prod.Lex.right; omega

  case eq k1 t1 t2 =>
    cases rhsTy <;> try simp at h
    split at h <;> try simp at h
    case _ v h1 =>
      rcases h1 with ⟨h1, h2⟩; cases h; simp; case _ v =>
      generalize zdef : (insert v (varsEqns tl)).card = z at *
      simp [Finset.card_insert_eq_ite] at zdef
      let σ : Subst Ty := ⟨λ y => if v = y then su (.eq k1 t1 t2) else su t#y⟩
      simp [isNotAll] at h2
      have h1' := h1
      simp [not_in_freeVars_iff_not_FV v h2.1] at h1
      simp [not_in_freeVars_iff_not_FV v h2.2] at h1
      have lem := var_not_free_after_subst_on_eqns
                   (eqns := tl) (s := .eq k1 t1 t2) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      have lem2 := freevars_after_subst_on_eqns
                   (eqns := tl) (s := .eq k1 t1 t2) (x := v) (σ := σ)
                   (by intro h; cases h; apply h1.1; assumption; apply h1.2; assumption)
                   (by simp [UnifyStateWf] at invh; intro t h; apply invh.2.2; grind)
                   (by simp [isNotAll]; apply h2) (by simp [σ])
      simp at lem2 lem;
      split at zdef <;> subst zdef
      case _ d =>
        have lem5 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v}))  < (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind

        apply Prod.Lex.left;
        replace lem6 := Finset.card_lt_card lem6
        grind;
      case _ d =>
        apply Prod.Lex.left;
        replace lem2 := Finset.card_le_card lem2
        have lem6 : (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl \ {v})) = (t1.freeVars ∪ (t2.freeVars ∪ varsEqns tl))  := by grind
        grind
    case _ a3 a4 =>
      split at h <;> try simp at h
      case _ e =>
        simp at e; subst e
        cases h; simp [size];
        have e : (t1.freeVars ∪ (t2.freeVars ∪ (a3.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card =
                       (t1.freeVars ∪ (a3.freeVars ∪ (t2.freeVars ∪ (a4.freeVars ∪ varsEqns tl)))).card := by grind
        rw[e]; apply Prod.Lex.right; omega

  case all =>  cases rhsTy  <;> try simp [isNotAll] at h

def loopUnify (u : UnifyState) : Option (Subst Ty) :=
  if h : u.nonEmptyEqns
  then
    if h1 : UnifyStateWf u then
    match h2 : unifyStep u ⟨h, h1⟩ with
    | .ok u' => loopUnify u'
    | .error _ => none
    else none
  else return u.subst
termination_by (UnifyStateSize u)
decreasing_by apply loopUnifyDecreases ⟨h, h1⟩ h2

@[simp]
abbrev EqnsUnifier (σ : Subst Ty) : List (Ty × Ty) -> Prop
| .nil => True
| .cons (t, u) l => Unifier σ t u ∧ EqnsUnifier σ l


def UnifierOfSubst (σ σ' : Subst Ty) : Prop := ∀ (x : Nat), σ.inner x = (σ'.inner x)[σ]
def UnifierIdempotent (σ : Subst Ty) : Prop := UnifierOfSubst σ σ

def UnifierOfUnifyState (σ' : Subst Ty) (u : UnifyState) : Prop :=
  UnifierOfSubst σ' u.subst ∧ EqnsUnifier σ' u.equations

theorem unifyFails_implies_unifyStep_error (h : u.nonEmptyEqns ∧ UnifyStateWf u) :
  (u = ⟨σ, (t1, t2) :: l⟩) ->
  unifyFails t1 t2 -> (∃ e, unifyStep u h = .error e)
:= by
  intro e h
  subst e; cases t1 <;> cases t2 <;> try simp [unifyStep, unifyFails] at *
  case _ k1 t1 u1 k2 t2 u2 _ =>
  have e : (k1 = k2) = False := by grind
  simp [e]

theorem UnifierIdempotent_extension :
  UnifierIdempotent σ ->
  (σ.act i) = t#i ->
  i ∉ t ->
  UnifierIdempotent (σ ∘ ⟨λ y => if i = y then su t else .su t#y⟩) := by sorry


theorem unifyStep_idempotency {u u': UnifyState} (precon : u.nonEmptyEqns ∧ UnifyStateWf u)
  (hi : UnifierIdempotent u.subst) :
  unifyStep u precon = .ok u' -> UnifierIdempotent u'.subst
:= by
  intro h
  rcases u with ⟨u, l⟩
  revert precon hi
  apply eqns_ind l
  · simp [UnifyState.nonEmptyEqns]
  · intro l x t ih precon hi h;
    simp  at h; split at h <;> try simp at h
    case _ h1 =>
    cases h
    simp at hi; simp;
    rcases h1 with ⟨h1, h2⟩
    simp [not_in_freeVars_iff_not_FV x h2] at h1
    apply UnifierIdempotent_extension hi _ h1
    sorry
  · intro l x t h1 ih precon hi h
    simp  at h; split at h <;> try simp at h
    case _ h1 =>
    cases h
    simp at hi; simp;
    rcases h1 with ⟨h1, h2⟩
    simp [not_in_freeVars_iff_not_FV x h2] at h1
    apply UnifierIdempotent_extension hi _ h1
    sorry
  · intro l x y ih precon hi h
    simp at h;
    split at h <;> try simp at h
    case _ e =>
    subst e; cases h; grind
  all_goals try (
  · intro l _ _ _ _ ih precon hi h
    simp at h; cases h; grind)
  · intro l _ _ _ _ _ ih precon hi h
    simp at h; cases h; grind
  · intro l t1 t2 ih precon hi h
    have lem := unifyFails_implies_unifyStep_error (l := l) (t1 := t1) (t2 := t2) (u := { subst := u, equations := (t1, t2) :: l : UnifyState}) precon rfl ih
    rcases lem with ⟨e, lem⟩; simp only [lem] at h; cases h



theorem unifyStep_sound {u u': UnifyState} (h : u.nonEmptyEqns ∧ UnifyStateWf u) (σ : Subst Ty) :
  unifyStep u h = .ok u' -> UnifierOfUnifyState σ u' -> UnifierOfUnifyState σ u
:= by
  intro h1
  rcases u with ⟨τ, l⟩
  revert h
  apply eqns_ind l

  · intro inv h uus
    simp at h; simp [UnifyState.nonEmptyEqns] at inv

  · intro l x t ih inv h uus
    simp at h; split at h <;> try simp at h
    case _ h1 =>
    cases h
    simp [UnifierOfUnifyState, Unifier]
    simp [UnifierOfUnifyState] at uus
    sorry

  · sorry

  · intro l x y ih inv h uus;
    simp at h; split at h <;> try simp at h
    case _ e =>
    subst e; cases h
    simp [UnifierOfUnifyState]
    simp [UnifierOfUnifyState] at uus
    simp [Unifier]; apply uus
  all_goals try (
  · intro l _ _ _ _ ih inv h uus
    simp at h; cases h
    simp [UnifierOfUnifyState, Unifier];
    simp [UnifierOfUnifyState, Unifier] at uus
    grind
  )
  · intro l _ _ _ _ _ ih inv h uus
    simp at h; cases h
    simp [UnifierOfUnifyState, Unifier];
    simp [UnifierOfUnifyState, Unifier] at uus
    grind
  · intro l t u ih inv h uus
    have lem := unifyFails_implies_unifyStep_error (l := l) (t1 := t) (t2 := u) (u := { subst := τ, equations := (t, u) :: l : UnifyState}) inv rfl ih
    rcases lem with ⟨e, lem⟩; simp only [lem] at h; cases h

theorem loopUnify_idempotency {σ  : Subst Ty} {u : UnifyState}
  (hi : UnifierIdempotent u.subst) (h : loopUnify u = some σ) : UnifierIdempotent σ
:= by
  unfold loopUnify at h;
  split at h
  case _ h1 =>
    split at h
    case _ h2 =>
      generalize zdef : unifyStep u _ = z at *
      cases z
      case error => simp at h
      case ok u' =>
      simp at h; replace hi := unifyStep_idempotency ⟨h1, h2⟩ hi zdef
      apply loopUnify_idempotency hi h
    case _ => simp at h
  case _ h1 => cases h; apply hi
termination_by (UnifyStateSize u)
decreasing_by case _ e1 e2 _ _ => -- for some reason lean cannot figure this one out
  simp at h; apply loopUnifyDecreases ⟨e1, e2⟩ zdef


theorem loopUnify_sound {σ  : Subst Ty} {u : UnifyState} (hi : UnifierIdempotent u.subst) :
  loopUnify u = some σ -> UnifierOfUnifyState σ u
:= by
  intro h
  have hi1 := loopUnify_idempotency hi h

  fun_induction loopUnify generalizing σ  <;> try simp at h
  case _ invh1 invh2 u' uss ih =>
    have lem := unifyStep_idempotency ⟨invh1, invh2⟩ hi uss
    replace uss' := unifyStep_sound _ σ uss
    apply uss'
    apply ih lem h hi1
  case _  u invh2 =>
    subst h;
    rcases u with ⟨us, ueqs⟩; simp at hi1
    simp [UnifyState.nonEmptyEqns] at invh2;
    simp [UnifierOfUnifyState]; simp [UnifierIdempotent] at hi
    subst ueqs
    apply And.intro
    · apply hi
    · simp [EqnsUnifier]

def unify (t u : Ty) : Option (Subst Ty) :=
  loopUnify ⟨Subst.id Ty, [(t, u)]⟩

theorem Subst.id_idempotent : UnifierIdempotent (Subst.id Ty)
:= by
  simp [UnifierIdempotent, UnifierOfSubst]
  intro x; cases x <;> simp [Subst.id] at *

theorem Subst.id_wf {t u : Ty} (h1 : t.isNotAll) (h2 : u.isNotAll) : UnifyStateWf (⟨Subst.id Ty, [(t, u)]⟩) = true := by simp [UnifyStateWf]; grind

theorem unify_soundness {t u : Ty} {σ  : Subst Ty}
  : unify t u = some σ -> Unifier σ t u
:= by
  intro h
  unfold unify at h
  replace h := loopUnify_sound (Subst.id_idempotent) h
  simp [UnifierOfUnifyState] at h; rcases h with ⟨h1, h2⟩
  apply h2


-- theorem unify_completeness {t u : Ty} {σ  : Subst Ty} :
--   Unifier σ t u -> unify t u = some σ'
--   -> ∃ (τ : Subst Ty), σ = σ' ∘ τ := by sorry


theorem Unifier.kinded :
  G&Δ ⊢ t : K ->
  G&Δ ⊢ u : K ->
  Unifier σ t u ->
  ∀ i : Nat, (hi : i < Δ.length) -> ∃ K, G&Δ ⊢ (σ.act i) : K
| .var j1, j => by
  intro u i hi; simp [Unifier] at u; sorry
| j, .var j1 => sorry
| .app j1a j2a, .app j1b j2b => by
  intro u i hi; simp [Unifier] at u;

  sorry
| _, _ => sorry


-- what about well kindedness?
-- we may want to have something like:
-- G,Δ ⊢ σ = ∀ i, ∃ k, G,Δ ⊢ (σ.act i).from_action : K
-- what is the theorem that we would like to write?
-- G&Δ ⊢ T : K ∧ G&Δ ⊢ σ -> G&Δ ⊢ T[σ] : K
theorem Unifier.substituion_lemma :
  G&Δ ⊢ t : K ->
  G&Δ ⊢ u : K ->
  Unifier σ t u ->
  G&Δ ⊢ t[σ] : K
| .var j1, j => by
  intro u; simp [Unifier] at u; simp; sorry
| j, .var j1 => sorry
| .app j1a j2a, .app j1b j2b => by
  intro u; simp [Unifier] at u;
  simp; rcases u with ⟨u1, u2⟩
  apply Kinding.app
  sorry
  sorry
  sorry

| _, _ => sorry


end Core.Ty
