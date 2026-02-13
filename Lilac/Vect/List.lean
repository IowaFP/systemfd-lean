
import Lilac.Vect.Definition

@[coe, simp]
def Vect.from_list : {n : Nat} -> (ℓ : List A) -> (ℓ.length = n) -> Vect n A
| 0, [], _ => nil
| n + 1, .cons x tl, h => x :: @from_list _ _ tl (by simp at h; exact h)

instance : CoeDep (List A) [] (Vect 0 A) where
  coe := Vect.nil

instance : CoeDep (List A) [t1] (Vect 1 A) where
  coe := Vect.from_list [t1] rfl

instance : CoeDep (List A) [t1, t2] (Vect 2 A) where
  coe := Vect.from_list [t1, t2] rfl

instance : CoeDep (List A) [t1, t2, t3] (Vect 3 A) where
  coe := Vect.from_list [t1, t2, t3] rfl

instance : CoeDep (List A) [t1, t2, t3, t4] (Vect 4 A) where
  coe := Vect.from_list [t1, t2, t3, t4] rfl

instance : CoeDep (List A) [t1, t2, t3, t4, t5] (Vect 5 A) where
  coe := Vect.from_list [t1, t2, t3, t4, t5] rfl

instance : CoeDep (List A) [t1, t2, t3, t4, t5, t6] (Vect 6 A) where
  coe := Vect.from_list [t1, t2, t3, t4, t5, t6] rfl

-- Adapted from Lean Prelude
@[app_unexpander Vect.nil]
meta def Vect.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `([])

-- Adapted from Lean Prelude
@[app_unexpander Vect.cons]
meta def Vect.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `([])      => `([$x])
  | `([$xs,*]) => `([$x, $xs,*])
  | `(⋯)       => `([$x, $tail])
  | _          => throw ()
| _ => throw ()
