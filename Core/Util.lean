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

theorem Ren.add_compose_distributes [RenMap T] [SubstMap T T][SubstMapId T T] {y z : Nat} :
  Ren.to (T := T) (λ x => x + y + z) = Subst.compose (T := T) (Ren.to (λ x => x + y)) (Ren.to (λ x => x + z))
:= by
  funext; case _ x =>
  simp [Ren.to, Subst.compose]

theorem Ren.add_one_commutes [RenMap T] [SubstMap T T] [SubstMapId T T] {y : Nat} :
  (Ren.to (T := T) (λ x => x + y)) ∘ Ren.to (T := T) (λ x => x + 1) = Subst.compose (+1) (Ren.to (T := T) (λ x => x + y))
:= by
  funext; case _ x =>
  simp [Ren.to, Subst.compose]; omega

def List.rmap [i : RenMap S] (r : Ren) : List S -> List S
| [] => []
| .cons x tl => (i.rmap r x) :: rmap r tl

instance [RenMap S] : RenMap (List S) where
  rmap := List.rmap

def List.smap [RenMap T] [SubstMap S T] (σ : Subst T) : List S -> List S
| [] => []
| .cons x tl => x[σ:_] :: smap σ tl

instance SubstMap_List  [RenMap T] [SubstMap S T] : SubstMap (List S) T where
  smap := List.smap

@[simp]
theorem List.smap_nil [RenMap T] [SubstMap S T] {σ : Subst T} : (@List.nil S)[σ:_] = [] := by
  simp [SubstMap.smap, List.smap]

@[simp]
theorem List.smap_cons [RenMap T] [SubstMap S T] {x} {tl : List S} {σ : Subst T}
  : (x :: tl)[σ:_] = x[σ:_] :: tl[σ:_]
:= by
  simp [SubstMap.smap, List.smap]

instance [RenMap T] [SubstMap S T] [SubstMapId S T]
  : SubstMapId (List S) T
where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
  : SubstMapCompose (List S) T
where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

@[simp]
theorem Vec.map_of_smap_fix [SubstMap A T] {σ : Subst T} : {v : Vec A n} -> Vec.map (·[σ:_]) v = v[σ:_]
| .nil => by simp
| .cons hd tl =>
  have lem := Vec.map_of_smap_fix (σ := σ) (v := tl)
  by simp; exact lem

@[simp]
theorem rewrite3_append_su [RenMap T] [SubstMap T T] {σ τ : Subst T} :
  {v : Vec T n} ->
  Sequ.append_vec (Vec.map su v) σ ∘ τ = Sequ.append_vec (Vec.map su v[τ:_]) (σ ∘ τ)
| .nil => by simp [Sequ.append_vec]
| .cons hd tl =>
  have lem := rewrite3_append_su (σ := σ) (τ := τ) (v := tl)
  by simp [Sequ.append_vec]; rw [lem]

@[simp]
theorem rewrite3_append_re [RenMap T] [SubstMap T T] {σ τ : Subst T} :
  {v : Vec Nat n} ->
  Sequ.append_vec (Vec.map re v) σ ∘ τ = Sequ.append_vec (Vec.map (λ i => τ i) v) (σ ∘ τ)
| .nil => by simp [Sequ.append_vec]
| .cons hd tl =>
  have lem := rewrite3_append_re (σ := σ) (τ := τ) (v := tl)
  by simp [Sequ.append_vec]; rw [lem]

def Subst.add (k : Nat) : Subst T := λ n => re (n + k)

@[simp]
theorem Subst.add_1 : @Subst.add T 1 = +1 := by unfold add; funext; simp

@[simp]
theorem Subst.add_0 : @Subst.add T 0 = Ren.id := by unfold Subst.add; funext; simp

@[simp]
theorem rewrite4_append [RenMap T] [SubstMap T T] {v : Vec (Subst.Action T) n}
  : (Subst.add n) ∘ (Sequ.append_vec v σ) = σ
:= by
  funext; case _ i =>
  induction i <;> simp [Subst.compose, Subst.add] at *
  case _ =>
    induction v <;> simp [Sequ.append_vec] at *
    assumption
  case _ k ih1 =>
    induction v <;> simp [Sequ.append_vec] at *
    case _ k' σ' v' ih2 =>
      apply ih2
      have lem : k + (k' + 1) = (k + k') + 1 := by omega
      rw[lem] at ih1; clear lem
      simp at ih1; apply ih1

theorem rename_range [RenMap T] [SubstMap T T] (k : Nat) :
  (Vec.map (@Subst.add T k) (Vec.range.go n p)) = (Vec.map re (Vec.range.go n (p + k)))
:= by
  induction n generalizing k p
  case zero => simp[Vec.range.go]
  case succ n ih =>
    simp[Vec.range.go];
    constructor
    simp[Subst.add]
    rw[ih (p := p + 1)]
    have lem : p + 1 + k = p + k + 1 := by omega
    rw[lem]


@[simp]
theorem rewrite_lift_n [RenMap T] [RenMapId T] [RenMapCompose T] [SubstMap T T] [SubstMapId T T] [SubstMapStable T][SubstMapCompose T T] {σ : Subst T}
  : σ.lift n = Sequ.append_vec (Vec.map re $ Vec.range n) (σ ∘ Subst.add n)
:= by
  induction n generalizing σ
  case zero =>
    have lem := Subst.rewrite_lift_zero (σ := σ)
    rw[Subst.rewrite_lift_zero]
    simp; simp [Vec.range.go, Sequ.append_vec]
  case succ n ih =>
    have lem := Subst.rewrite_lift_succ (σ := σ) (k := n)
    rw[lem]; simp; rw[ih]
    simp[Vec.range.go, Sequ.append_vec];
    have lem1 : @Subst.add T n ∘ +1 = Subst.add (n + 1) := by unfold Subst.add; rfl
    rw[lem1, <-rename_range (T := T) (n := n) (p := 0) 1]
    rfl


@[simp]
theorem rewrite_vec_map_range_1 : Vec.map (@re T) (Vec.range 1) = #𝓋[re 0] := by
  simp [Vec.map, Vec.range, Vec.range.go]

@[simp]
theorem rewrite_append_over_range {v : Vec (Subst.Action T) n}
  : Vec.map (Sequ.append_vec v +0) (Vec.range n) = v
:= by
  induction n <;> simp at *
  case zero => simp [Vec.range.go]; symm; cases v; rfl
  case succ ih =>

    sorry

   -- induction v <;> simp [Vec.range.go]
   -- case _ i σ σv ih =>
   -- constructor
   -- simp[Sequ.append_vec]
   -- simp[Sequ.append_vec];
   -- unfold Vec.range.go at ih;
   -- sorry

@[simp]
theorem rewrite_cons_over_range
  : Vec.map (a::+0) (Vec.range 1) = #𝓋[a]
:= by simp [Vec.range.go]

@[simp]
theorem rewrite_append_singleton
  : Sequ.append_vec #𝓋[a] σ = a::σ
:= by simp [Sequ.append_vec]

@[simp]
theorem List.subst_append [RenMap T] [SubstMap T T] {a b : List T} {σ : Subst T}
  : (a ++ b)[σ:T] = a[σ:T] ++ b[σ:T]
:= by
   induction a <;> simp at *
   assumption


@[simp]
theorem Vec.subst_to_list [RenMap T] [SubstMap T T] {v : Vec T n} {σ : Subst T}
  : (Vec.to_list v)[σ:_] = Vec.to_list v[σ:_]
:= by
   induction v <;> simp [Vec.to_list] at *
   assumption


theorem Vec.subst_to_cons [RenMap T] [SubstMap T T] {hd : T} {tl : Vec T n} :
  (Vec.cons hd tl)[σ:T] = .cons (hd[σ:T]) (tl[σ:T]) := by simp


@[grind =]
theorem Fun.Vec.subst_to [RenMap T] [SubstMap T T] {v : Fun.Vec T n}
  : (v.to)[σ:T] = Fun.Vec.to (λ i => (v i)[σ:T])
:= by
  induction v using Fun.Vec.induction
  simp [Fun.Vec.to]; rfl
  case _ ih =>
  simp [Fun.Vec.to]; rw[Fun.Vec.induction_cons]; simp;
  simp [Fun.Vec.to] at ih; rw[ih]
  sorry


  -- induction n
  -- sorry
  -- sorry
  -- induction v.to
  -- simp; rw[Fun.Vec.eta0 (v := v)]; sorry
  -- sorry
   -- apply v.induction
   -- case nil => simp; sorry
   -- case cons =>
   --   intro n hd tl ih
   --   simp; sorry


@[simp, grind =]
theorem List.getElem?_subst [RenMap T] [SubstMap S T] {ℓ : List S} {σ : Subst T} {x : Nat}
  : ℓ[x]?[σ:T] = ℓ[σ:T][x]?
:= by
  induction ℓ generalizing x <;> simp
  case _ hd tl ih => cases x <;> simp [*]
