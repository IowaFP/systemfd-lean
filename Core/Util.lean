import LeanSubst

open LeanSubst

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
