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
  (∀ v, ¬ t = Option.some v) <->
  t = .none
:= by
apply Iff.intro
· intro h
  cases t; simp
  case _ v => exfalso; apply h v rfl
· intro h a h1; simp [h1] at h


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

@[simp, grind =]
theorem List.length_rmap [RenMap S T] {ℓ : List S} {r : Ren T} : ℓ⟨r⟩.length = ℓ.length := by
  induction ℓ <;> simp [*]

@[simp, grind =]
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

@[simp]
theorem Vec.map_of_smap_fix [SubstMap A T] {σ : Subst T} : {v : Vec A n} -> Vec.map (λ (x : A) => x[σ]) v = v[σ]
| .nil => by simp
| .cons hd tl =>
  have lem := Vec.map_of_smap_fix (σ := σ) (v := tl)
  by simp; exact lem

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


@[simp, grind =]
theorem List.getElem_rmap [RenMap S T] {r : Ren T} {ℓ : List S} (h1 : i < ℓ.length) :
  ℓ⟨r⟩[i]'(by grind) = ℓ[i]⟨r⟩
  := by rw[List.getElem_eq_iff]; rw[<-List.getElem?_rmap]; grind

@[simp, grind =]
theorem List.getElem_smap [SubstMap S T] {s : Subst T} {ℓ : List S} (h1 : i < ℓ.length) :
  ℓ[s][i]'(by grind) = ℓ[i][s]
  := by rw[List.getElem_eq_iff]; rw[<-List.getElem?_smap]; grind


theorem subst_lift [RenMap T T] [RenMapId T T] [RenMapCompose T T] (σ : Subst T) :
  x < n ->
  (σ.lift n).act x = re x
:= by
  intro h; induction n generalizing x σ; cases h
  case _ n ih =>
  cases x; simp [Subst.lift]
  case _ i =>
  have lem : i < n := by omega
  replace ih := @ih i σ lem
  rw [Subst.rewrite_lift_succ]
  generalize zdef : σ.lift n = z at *
  simp [Subst.lift]; rw [ih]; simp

theorem List.length_gt_zero_exists : {l : List α} -> (h : l.length > 0) ->
 ∃ (a : α) (l' : List α), l = (a :: l')
| .nil, j => by simp at j
| .cons a as, j => by simp



theorem quantifier_bundle :
  (∀ (a : α) (b : β) , ¬ t = .some (a, b)) <-> ∀ (h : α × β), ¬ t = some h
  := by
  apply Iff.intro
  · intro h p h1
    replace h := h p.1 p.2; simp at h; apply h h1
  · intro h a b;
    apply h (a, b)

theorem List.filter_gt_0 {f : α -> Bool} {l : List α} {i : Nat} (h : i < l.length):
  f l[i] -> (l.filter f).length > 0
:= by
  intro h1
  induction l generalizing i <;> simp at *
  cases h; case _ hd tl ih =>
  cases i
  case zero =>
    simp at h1; apply Or.inl h1
  case succ n =>
    simp at h1; simp at h;
    apply Or.inr
    apply ih h h1

theorem List.filter_set_neq {f : α -> Bool} {l : List α} {a : α} (i : Nat) (h : i < l.length) :
  f l[i] -> ¬ f a ->
  (List.filter f (l.set i a)).length = (List.filter f l).length - 1
:= by
intro h1 h2
induction l generalizing i <;> simp at *
case _ hd tl ih =>
  cases i <;> simp at *
  · rw[List.filter_cons]; rw[List.filter_cons];
    rw[h2]; simp
    conv =>
      rhs
      rw[ite_cond_eq_true (h := by grind)]
    simp
  case succ n =>
    simp at h
    replace ih := @ih n h h1
    rw[List.filter_cons]; rw[List.filter_cons]
    generalize zdef : f hd = z at *
    cases z <;> simp at *
    · apply ih
    · rw[ih]
      have lem : (filter f tl).length > 0 := by apply List.filter_gt_0 h h1
      omega



theorem List.zipIdx_set {l : List α} {a : α} {i : Nat} (h : i < l.length) :
  (l.set i a).zipIdx k = (l.zipIdx k).set i (a, (i + k))
:= by
  induction l generalizing i k <;> simp at *
  case _ hd tl ih =>
  cases i
  case zero => simp
  case succ n =>
    simp at *
    have lem : n + 1 + k = n + (k + 1) := by omega
    replace ih := @ih (k + 1) n h; rw[lem]; apply ih

@[grind =]
theorem List.zipIdx_length {l : List α} :
  l.length = l.zipIdx.length := by induction l <;> simp at *


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


inductive VecTyping (J : A -> B -> Prop) : Vec A m -> Vec B m -> Prop
| nil : VecTyping J .nil .nil
| cons :
  J a b ->
  VecTyping J as bs ->
  VecTyping J (a::as) (b::bs)


namespace List

theorem flatten_idx_getElem {ll : List (List α)} {l : List α} :
  ll.flatten = l ->
  ∀ i : Nat, l[i]? = some a ->
  ∃ (i' j' : Nat) (l' : List α), (ll[i']? = some l' ∧ l'[j']? = some a) :=
by
intro h1 i h2
fun_induction List.flatten generalizing l i <;> simp at *
case _ => subst l; exfalso; simp at h2
case _ l ll ih =>
  subst l
  cases Nat.decLt i l.length
  case _ h =>
    rw[List.getElem?_append_right (by grind)] at h2;
    replace ih := ih (i - l.length) h2
    rcases ih with ⟨i', j', l', ih⟩
    exists i' + 1; simp; exists j'; exists l'
  case _ h =>
    rw[List.getElem?_append_left (hn := h)] at h2;
    exists 0; exists i; exists l

theorem List.mapM_length {f : α -> Option β} {Γ : List α} {Δ : List β} :
  Γ.mapM f = some Δ ->
  Γ.length = Δ.length
:= by
intro h
rw[<-List.mapM'_eq_mapM] at h
fun_induction mapM' generalizing Δ <;> simp at *
subst h; simp
case _ g Γ' ih =>
  simp [Option.bind_eq_some_iff] at h; rcases h with ⟨d, h, Δ', h2, e⟩; subst e
  simp; apply ih h2

theorem mapM_getElem? {f : α -> Option β} {Γ : List α} {Δ : List β} :
  (h : Γ.mapM f = some Δ) ->
  ∀ (j : Nat), (hj : j < Δ.length) ->
  f (Γ[j]'(by rw[<-List.mapM_length h] at hj; apply hj)) = some (Δ[j]'hj)
:= by
intro h j hj
rw[<-List.mapM'_eq_mapM] at h
fun_induction mapM' generalizing Δ j <;> simp at *
subst h; simp at hj
case _ g Γ' ih h1 =>
simp [Option.bind_eq_some_iff] at h; rcases h with ⟨d, h, h2, h3, e⟩
subst e; simp at hj
cases j <;> simp
apply h
apply ih; rw[<-List.mapM'_eq_mapM]; apply h3; apply h3


end List
