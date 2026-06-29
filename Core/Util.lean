import Lilac
import LeanSubst
import Lean.Parser
import Core.Vec

open Lilac
open LeanSubst

macro t:term " ▸ " tac:Lean.Parser.Tactic.tacticSeq : term => `(cast (by $tac) $t)

def ExistsUnique {α : Sort u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

theorem get!_option2_eq_some {a : Option (Option T)}
  : a.get! = some t -> a = t
:= by
  intro h
  cases a <;> simp at *
  exact h

@[simp]
def prefix_equal [BEq T] : List T -> List T -> Option (List T)
| [], t => .some t
| .cons _ _, [] => .none
| .cons x1 t1, .cons x2 t2 => if x1 == x2 then prefix_equal t1 t2 else .none

theorem prefix_equal_law [BEq T] [LawfulBEq T] {p t1 t2 : List T}
  : prefix_equal t1 t2 = some p -> t2 = t1 ++ p
:= by
intro h
induction t1, t2 using prefix_equal.induct generalizing p
case _ => simp at h; subst h; simp
case _ => simp at h
case _ h2 ih =>
    replace h2 := LawfulBEq.eq_of_beq h2; subst h2
    simp at h; rw [ih h]; simp
case _ h2 =>
  simp at *; exfalso
  apply h2; apply h.1

instance : Monad List where
  pure a := List.cons a List.nil
  bind l f := List.flatten (List.map f l)

theorem option_lemma :
  (∀ v, ¬ t = Option.some v) ->
  t = .none
:= by
intro h
cases t; simp
case _ v => exfalso; apply h v rfl

theorem not_eq_of_beq [BEq T] [LawfulBEq T] {x y : T} : ¬ ((x == y) = true) -> x ≠ y := by
intro h1 h2; subst h2; apply h1; simp

@[simp]
def rep (f : T -> T) (x : T) : Nat -> T
| 0 => x
| n + 1 => f (rep f x n)

theorem List.reverse_ind :
  {motive : List T -> Prop} ->
  (ℓ : List T) ->
  (nil : motive []) ->
  (rcons : ∀ hd tl, motive tl -> motive (tl ++ [hd])) ->
  motive ℓ
:= by
  intro P ℓ h1 h2
  generalize zdef : reverse ℓ = z at *
  induction z generalizing ℓ
  case nil => simp at zdef; subst zdef; apply h1
  case cons hd tl ih =>
    have lem : ℓ.reverse.reverse = (hd :: tl).reverse := by rw [zdef]
    simp at lem; rw [lem]; apply h2 _ _
    apply ih; simp

theorem List.indexing_length_some {t : T} {Δ : List T} {x : Nat} :
  Δ[x]? = some t ->
  x < Δ.length := match x, Δ with
| n, [] => by
  intro h; simp at h;
| 0, .cons t Δ => by
  intro h; simp
| n + 1, .cons _ Δ => by
  intro h; simp at h;
  simp; apply List.indexing_length_some (t := t) (Δ := Δ) (x := n) h

@[simp]
theorem List.length_rmap [RenMap S T] {ℓ : List S} {r : Ren T} : ℓ⟨r⟩.length = ℓ.length := by
  induction ℓ <;> simp [*]

@[simp]
theorem List.length_smap [SubstMap S T] {ℓ : List S} {σ : Subst T} : ℓ[σ].length = ℓ.length := by
  induction ℓ <;> simp [*]

@[simp]
theorem List.map_su_eq {ℓ1 ℓ2 : List T} : (ℓ1.map su = ℓ2.map su) = (ℓ1 = ℓ2) := by
  induction ℓ1 generalizing ℓ2; simp
  case _ hd tl ih =>
  cases ℓ2; simp at *; case _ hd2 tl2 =>
  simp [*]

@[simp]
theorem Vec.list_eq {v1 v2 : Vec α n} : (v1.list = v2.list) = (v1 = v2) := by
  induction v1
  case _ => cases v2; simp
  case _ hd tl ih =>
  cases v2; simp at *; case _ hd2 tl2 =>
  simp [*]

-- theorem Ren.add_compose_distributes [RenMap T] [SubstMap T T][SubstMapId T T] {y z : Nat} :
--   Ren.to (T := T) (λ x => x + y + z) = Subst.compose (T := T) (Ren.to (λ x => x + y)) (Ren.to (λ x => x + z))
-- := by
--   funext; case _ x =>
--   simp [Ren.to, Subst.compose]

-- theorem Ren.add_one_commutes [RenMap T] [SubstMap T T] [SubstMapId T T] {y : Nat} :
--   (Ren.to (T := T) (λ x => x + y)) ∘ Ren.to (T := T) (λ x => x + 1) = Subst.compose (+1) (Ren.to (T := T) (λ x => x + y))
-- := by
--   funext; case _ x =>
--   simp [Ren.to, Subst.compose]; omega

@[simp]
theorem Vec.map_of_smap_fix [SubstMap A T] {σ : Subst T} : {v : Vec A n} -> Vec.map (λ (x : A) => x[σ]) v = v[σ]
| .nil => by simp
| .cons hd tl =>
  have lem := Vec.map_of_smap_fix (σ := σ) (v := tl)
  by simp; exact lem

-- @[grind =]
-- theorem Fun.Vec.subst_to [RenMap T] [SubstMap T T] {v : Fun.Vec T n}
--   : (v.to)[σ:T] = Fun.Vec.to (λ i => (v i)[σ:T]) := sorry

@[simp, grind =]
theorem List.getElem?_rmap [RenMap S T] {ℓ : List S} {r : Ren T} {x : Nat}
  : ℓ[x]?⟨r⟩ = ℓ⟨r⟩[x]?
:= by
  induction ℓ generalizing x <;> simp
  case _ hd tl ih => cases x <;> simp [*]

@[simp, grind =]
theorem List.getElem?_smap [SubstMap S T] {ℓ : List S} {σ : Subst T} {x : Nat}
  : ℓ[x]?[σ] = ℓ[σ][x]?
:= by
  induction ℓ generalizing x <;> simp
  case _ hd tl ih => cases x <;> simp [*]

----------------------------------------------------------------------------------------------------
--- To be added to LeanSubst
----------------------------------------------------------------------------------------------------
macro "subst_solve_compose_fix" : tactic => `(tactic| {
  intro s σ τ
  induction s generalizing σ τ
  any_goals solve | simp +instances [*]
  try any_goals solve | (
    try simp [-Subst.rewrite_lift, -Subst.rewrite_lift_ren, -Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
    try funext; case _ x =>
    try simp [-Subst.rewrite_lift, -Subst.rewrite_lift_ren, -Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
    try grind)
})

namespace LeanSubst
  @[simp]
  theorem Subst.Vec.rmap_list [RenMap S T] {v : Vec S n} {r : Ren T} : v.list⟨r⟩ = v⟨r⟩.list := by
    induction v <;> simp [*]

  @[simp]
  theorem Subst.Vec.smap_list [SubstMap S T] {v : Vec S n} {σ : Subst T} : v.list[σ] = v[σ].list := by
    induction v <;> simp [*]
end LeanSubst
