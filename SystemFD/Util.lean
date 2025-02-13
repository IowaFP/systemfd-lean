
@[simp]
def prefix_equal [BEq T] : List T -> List T -> Option (List T)
| [], t => .some t
| .cons _ _, [] => .none
| .cons x1 t1, .cons x2 t2 => if x1 == x2 then prefix_equal t1 t2 else .none

instance : Monad List where
  pure a := List.cons a List.nil
  bind l f := List.flatMap l f

theorem option_neg : (∀ l, ¬ (p = some l)) -> p = none := by
  intros np;
  cases p;
  case _ => simp
  case _ v => simp; exfalso; apply np v; rfl

theorem not_eq_of_beq [BEq T] [LawfulBEq T] {x y : T} : ¬ ((x == y) = true) -> x ≠ y := by
intro h1 h2; subst h2; apply h1; apply LawfulBEq.rfl
