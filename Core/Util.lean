import Init.GetElem

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
