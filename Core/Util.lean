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

  instance [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T] : SubstMapRenComposeLeft (List S) T where
    apply_ren_compose_left := by intro s r τ; induction s <;> simp [*]

  instance [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T] : SubstMapRenComposeRight (List S) T where
    apply_ren_compose_right := by intro s r τ; induction s <;> simp [*]

  @[simp, grind =]
  theorem Subst.rewrite3_cons_ren_fix [RenMap T T] [SubstMap T T] {σ : Subst T} {r : Ren T}
    : (a :: σ) ∘ r = a⟨r⟩:: (σ ∘ r)
  := by
    simp [cons, compose_ren_right]
    funext; case _ x =>
    cases x; all_goals simp [act, SubstAction.act]

  @[simp, grind =]
  theorem Subst.rewrite3_cons_ren_subst [SubstMap T T] {σ : Subst T} {r : Ren T}
    : (x :: r) ∘ σ = σ.act x :: (r ∘ σ)
  := by
    simp [cons, compose_ren_left]
    funext; case _ x =>
    cases x; all_goals simp [act, SubstAction.act]

  @[simp, grind =]
  theorem Subst.ren_succ_beta_to {r : Ren T}
    : (r ∘ Ren.succ T) ∘ (a :: Subst.id T) = r.to
  := by simp [compose_ren_left, Ren.to]

  theorem Ren.lift_of_succ_rev {r : Ren S} : r.lift (1 + k) = r.lift.lift k := by
    induction k; simp
    case _ k ih =>
    rw [Ren.lift_of_succ, <-ih, <-Ren.lift_of_succ]
    congr 1

  @[grind =]
  theorem Ren.lift_of_add {r : Ren S} : r.lift (a + b) = (r.lift a).lift b := by
    induction a generalizing b; simp
    case _ a ih =>
    rw [Ren.lift_of_succ]
    rw [<-Ren.lift_of_succ_rev]
    rw [<-ih]; congr 1; omega

  @[grind =]
  theorem Subst.compose_commute_add [RenMap T T] [SubstMap T T] [SubstMapStable T T] {τ : Subst T}
    : τ ∘ add T k = add T k ∘ τ.lift k
  := by
    simp [compose]; funext; case _ x =>
    generalize zdef : τ.act x = z
    cases z <;> simp
    rw [apply_stable]; simp

  @[grind =]
  theorem Subst.compose_commute_add_ren_subst [RenMap T T] [SubstMap T T] [SubstMapStable T T] {τ : Subst T}
    : τ ∘ Ren.add T k = Ren.add T k ∘ τ.lift k
  := by
    simp [compose_ren_right, compose_ren_left]

  @[grind =]
  theorem Subst.compose_commute_add_ren [RenMap T T] {r : Ren T}
    : r ∘ add T k = add T k ∘ r.lift k
  := by
    simp [compose_ren_left, compose_ren_right]

  @[grind =]
  theorem Subst.compose_commute_add_ren_ren {r : Ren T}
    : r ∘ Ren.add T k = .add T k ∘ r.lift k
  := by simp [Ren.compose]

  @[simp]
  theorem Ren.to_cons {r : Ren T} : (x::r).to = re x :: r.to := by
    simp [to, cons, Subst.cons]; funext; case _ x =>
    cases x <;> simp

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
  theorem Subst.rewrite4_cons_ren_add_direct {r : Ren T} {ℓ : List Nat}
    : Ren.add T ℓ.length ∘ (ℓ ++ r) = r
  := by simp [Ren.compose]

  @[simp, grind =]
  theorem Subst.rewrite4_cons_ren_add_indirect {r : Ren T} {ℓ : List Nat} {h : k = ℓ.length}
    : Ren.add T k ∘ (ℓ ++ r) = r
  := by simp [Ren.compose, h]

  @[simp, grind =]
  theorem Subst.rewrite4_append_add_direct {σ : Subst T} {ℓ : List (Action T)}
    : Ren.add T ℓ.length ∘ (ℓ ++ σ) = σ
  := by simp [compose_ren_left]; congr

  @[simp, grind =]
  theorem Subst.rewrite4_append_add_indirect {σ : Subst T} {ℓ : List (Action T)} {h : k = ℓ.length}
    : Ren.add T k ∘ (ℓ ++ σ) = σ
  := by simp [compose_ren_left, h]; congr

  theorem Subst.compose_ren_left_cons_lift_1 [RenMap T T] [SubstMap T T] {a : Action T} {r : Ren T} {σ : Subst T}
    : r.lift ∘ (a :: σ) = a :: (r ∘ σ)
  := by
    simp; congr 1

  @[simp]
  theorem Subst.compose_ren_left_cons_lift_k1 [RenMap T T] [SubstMap T T] {a : Action T} {r : Ren T}
    : r.lift (k + 1) ∘ (a :: σ) = a :: (r.lift k ∘ σ)
  := by
    rw [Ren.lift_of_succ, compose_ren_left_cons_lift_1]

  @[simp, grind =]
  theorem Subst.compose_ren_left_cons_lift_direct
    [RenMap T T] [SubstMap T T] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
    : r.lift ℓ.length ∘ (ℓ ++ σ) = ℓ ++ (r ∘ σ)
  := by
    induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

  @[simp, grind =]
  theorem Subst.compose_ren_left_cons_lift_indirect
    [RenMap T T] [SubstMap T T] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T} {h : k = ℓ.length}
    : r.lift k ∘ (ℓ ++ σ) = ℓ ++ (r ∘ σ)
  := by
    induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

  @[simp, grind =]
  theorem Subst.compose_ren_right_append [RenMap T T] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
    : (ℓ ++ σ) ∘ r = ℓ⟨r⟩ ++ σ ∘ r
  := by
    induction ℓ generalizing σ r <;> simp
    case _ hd tl ih =>
    rw [<-ih]; simp [compose_ren_right, cons]; funext; case _ i =>
    cases i <;> simp

  theorem Subst.compose_ren_right_assoc
    [RenMap S S] [SubstMap S S] [SubstMapRenComposeLeft S S]
    {σ τ : Subst S} {r : Ren S}
    : (σ ∘ r) ∘ τ = σ ∘ (r ∘ τ)
  := by
    simp [compose, compose_ren_left, compose_ren_right]; funext; case _ i =>
    generalize zdef : σ.act i = z
    cases z <;> simp
    congr

  theorem Subst.compose_ren_right_assoc2
    [RenMap S S] [SubstMap S S] [SubstMapRenComposeRight S S]
    {σ τ : Subst S} {r : Ren S}
    : (σ ∘ τ) ∘ r = σ ∘ (τ ∘ r)
  := by
    simp [compose, compose_ren_right]; funext; case _ i =>
    generalize zdef : σ.act i = z
    cases z <;> simp
    congr

  @[simp]
  theorem Subst.Vec.rmap_list [RenMap S T] {v : Vec S n} {r : Ren T} : v.list⟨r⟩ = v⟨r⟩.list := by
    induction v <;> simp [*]

  @[simp]
  theorem Subst.Vec.smap_list [SubstMap S T] {v : Vec S n} {σ : Subst T} : v.list[σ] = v[σ].list := by
    induction v <;> simp [*]

end LeanSubst
