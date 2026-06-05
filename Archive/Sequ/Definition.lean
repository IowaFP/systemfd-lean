
import Lilac.Map

namespace Lilac.Fun

def Sequ (A : Sort u) := Nat -> A

def Sequ.cons (head : A) (tail : Sequ A) : Sequ A
| 0 => head
| n + 1 => tail n

infixr:67 (name := sequ_cons) " :: " => Sequ.cons

@[simp]
theorem Sequ.cons_zero {tl : Sequ A} : (hd :: tl) 0 = hd := by simp [cons]

@[simp]
theorem Sequ.cons_succ {tl : Sequ A} : (hd :: tl) (n + 1) = tl n := by simp [cons]

def Sequ.head (s : Sequ A) : A := s 0

@[simp]
theorem Sequ.head_cons : head (hd :: tl) = hd := by simp [head, cons]

def Sequ.tail (s : Sequ A) : Sequ A
| n => s (n + 1)

@[simp]
theorem Sequ.tail_cons : tail (hd :: tl) = tl := by
  funext; case _ i => simp [tail]

def Sequ.uncons (s : Sequ A) : A ×' Sequ A := ⟨head s, tail s⟩

@[simp]
theorem Sequ.uncons_cons : uncons (hd :: tl) = ⟨hd, tl⟩ := by simp [uncons]

theorem Sequ.uncons_iff : uncons v = ⟨hd, tl⟩ <-> v = hd :: tl := by
  apply Iff.intro <;> intro h
  case _ =>
    unfold uncons at h
    injection h with e1 e2; subst e1 e2
    funext; case _ i =>
    induction i <;> simp [head, tail]
  case _ => subst h; simp

def Sequ.coiter {X : Sort u2} (hd : X -> A) (tl : X -> X) : X -> Sequ A
| x, 0 => hd x
| x, n + 1 => coiter hd tl (tl x) n

@[simp]
theorem Sequ.iter_head : head (coiter hd tl x) = hd x := by simp [coiter, head]

@[simp]
theorem Sequ.iter_tail : tail (coiter hd tl x) = coiter hd tl (tl x) := by
  funext; case _ i => simp [tail, coiter]

@[simp]
theorem Sequ.fold_id {v : Sequ A} : id <$> v = v := by rfl

theorem Sequ.map_compose {v : Sequ A} : f <$> (g <$> v) = (f ∘ g) <$> v := by rfl

end Lilac.Fun
