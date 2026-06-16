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

@[simp]
theorem List.subst_append [SubstMap S T] {a b : List S} {σ : Subst T}
  : (a ++ b)[σ] = a[σ] ++ b[σ]
:= sorry

@[simp]
theorem Vec.subst_to_list [SubstMap S T] {v : Vec S n} {σ : Subst T}
  : v.list[σ] = v[σ].list
:= sorry

-- @[grind =]
-- theorem Fun.Vec.subst_to [RenMap T] [SubstMap T T] {v : Fun.Vec T n}
--   : (v.to)[σ:T] = Fun.Vec.to (λ i => (v i)[σ:T]) := sorry

-- @[simp, grind =]
-- theorem List.getElem?_subst [RenMap T] [SubstMap S T] {ℓ : List S} {σ : Subst T} {x : Nat}
--   : ℓ[x]?[σ:T] = ℓ[σ:T][x]?
-- := by
--   induction ℓ generalizing x <;> simp
--   case _ hd tl ih => cases x <;> simp [*]

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
  theorem Subst.ren_to_hcompose [SubstMap S T] {r : Ren S} {σ : Subst T}: r.to ◾ σ = r.to := sorry

  @[simp]
  theorem Subst.ren_to_hcompose_ren [RenMap S T] {r : Ren S} {k : Ren T}: r.to ◾ k = r.to := sorry

  @[simp]
  theorem Subst.to_append {ℓ : List Nat} {r : Ren T} : (ℓ ++ r).to = ℓ ++ r.to := sorry

  @[grind =]
  theorem Subst.compose_commute_add [RenMap T T] [SubstMap T T] [SubstMapStable T T] {τ : Subst T}
    : τ ∘ add T k = add T k ∘ τ.lift k
  := by
    simp [compose]; funext; case _ x =>
    generalize zdef : τ.act x = z
    cases z <;> simp
    rw [apply_stable]; simp

  @[grind =]
  theorem Subst.compose_commute_add_ren [RenMap T T] {r : Ren T}
    : r ∘ add T k = add T k ∘ r.lift k
  := by
    simp [compose_ren_left, compose_ren_right]

  @[simp]
  theorem Ren.to_cons {r : Ren T} : (x::r).to = re x :: r.to := by
    simp [to, cons, Subst.cons]; funext; case _ x =>
    cases x <;> simp

  theorem Subst.rewrite1_append_ren_le {T s e} : s..e ++ +r e = .add T (min s e) := by
    induction e generalizing s; simp
    case _ e ih =>
    cases Nat.decLt s (e + 1)
    case _ h1 =>
      have lem : s ≥ e + 1 := by omega
      rw [Ren.range_ge_nil (h := lem)]; simp
      rw [Nat.min_eq_right lem]
    case _ h1 =>
      rw [Ren.range_lt_cons (h := h1)]
      rw [Nat.min_eq_left (by omega)]
      simp
      have lem : (s + 1)..(e + 1) ++ Ren.add T (e + 1) = .succ T ∘ (s..e ++ Ren.add T e) := sorry
      rw [lem, ih, Nat.min_eq_left (by omega)]
      sorry

  theorem Subst.rewrite1_append_le {T s e} : s..e ++ +σ e = add T (min s e) := by
    induction e generalizing s; simp
    case _ e ih =>
    cases Nat.decLt s (e + 1)
    case _ h1 =>
      have lem : s ≥ e + 1 := by omega
      rw [Ren.range_ge_nil (h := lem)]; simp
      rw [Nat.min_eq_right lem]
    case _ h1 =>
      rw [Ren.range_lt_cons (h := h1)]
      rw [Nat.min_eq_left (by omega)]
      simp
      have lem : (s + 1)..(e + 1) ++ add T (e + 1) = .succ T ∘ (s..e ++ add T e) := sorry
      rw [lem, ih, Nat.min_eq_left (by omega)]
      sorry

  @[simp, grind =]
  theorem Subst.rewrite1_append_ren : 0..e ++ +r e = .id T := by
    have lem := @rewrite1_append_ren_le T 0 e
    simp at lem; exact lem

  @[simp, grind =]
  theorem Subst.rewrite1_append : 0..e ++ +σ e = id T := by
    have lem := @rewrite1_append_le T 0 e
    simp at lem; exact lem

  @[simp, grind =]
  theorem Subst.rewrite_lift_ren : r.lift = 0::(r ∘ +1r) := by
    simp [Ren.lift, Ren.cons]; funext; case _ x =>
    cases x <;> simp

  @[simp, grind =]
  theorem Subst.rewrite3_append_ren_ren_cons {r1 r2 : Ren T}
    : (x::r1) ∘ r2 = r2.act x::(r1 ∘ r2)
  := by
    simp [Ren.cons, Ren.compose]; funext; case _ x =>
    cases x <;> simp

  @[simp, grind =]
  theorem Subst.rewrite3_append_ren_ren {ℓ : List Nat} {r1 r2 : Ren T}
    : (ℓ ++ r1) ∘ r2 = ℓ⟨r2⟩ ++ (r1 ∘ r2)
  := by
    induction ℓ generalizing r1 r2 <;> simp [*]

  @[simp]
  theorem range_act_succ_ren_fixed
    : (s..e)⟨.succ T⟩ = s.succ..e.succ
  := by
    induction e generalizing s; simp
    case _ e ih =>
      simp [Ren.range]; split <;> simp
      case _ h =>
      rw [ih]
      cases Nat.decLe (s + 1) e <;> simp [ite]
      case _ h2 =>
        rw [Ren.range_ge_nil]; omega
      case _ h2 =>
        conv =>
          lhs; simp [Ren.range]
        split <;> simp

  @[simp, grind =]
  theorem Subst.rewrite_lift_k_ren : r.lift k = 0..k ++ (r ∘ +r k) := by
    induction k generalizing r <;> simp
    case _ k ih =>
    rw [Ren.lift_of_succ, ih]; simp
    rw [<-Ren.compose_add_succ_right]

  @[simp, grind =]
  theorem Subst.ren_rewrite1 [RenMap T T] {r : Ren T} : id T ∘ r = r.to := sorry

end LeanSubst
