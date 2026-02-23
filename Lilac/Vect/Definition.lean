
import Lilac.Map

def Vect (n : Nat) (A : Sort u) := Fin n -> A

def Vect.nil : Vect 0 A := λ x => nomatch x

def Vect.cons (head : A) (tail : Vect n A) : Vect (n + 1) A :=
  Fin.cases (motive := λ _ => A) head tail

infixr:67 (name := vect_cons) " :: " => Vect.cons

@[simp]
theorem Vect.cons_zero {tl : Vect n A} : (hd :: tl) 0 = hd := by simp [cons]

@[simp]
theorem Vect.cons_succ {tl : Vect n A} : (hd :: tl) i.succ = tl i := by simp [cons]

@[simp]
theorem Vect.eta0 {v : Vect 0 A} : v = nil := by
  funext; case _ i =>
  apply Fin.elim0 i

def Vect.head (v : Vect (n + 1) A) : A := v 0

@[simp]
theorem Vect.head_cons : head (hd :: tl) = hd := by simp [head, cons]

def Vect.tail (v : Vect (n + 1) A) : Vect n A
| n => v (Fin.succ n)

@[simp]
theorem Vect.tail_cons : tail (hd :: tl) = tl := by
  simp [cons]; funext; case _ i => simp [tail]

def Vect.uncons (v : Vect (n + 1) A) : A ×' Vect n A := ⟨head v, tail v⟩

@[simp]
theorem Vect.uncons_cons : uncons (hd :: tl) = ⟨hd, tl⟩ := by simp [uncons]

theorem Vect.uncons_iff : uncons v = ⟨hd, tl⟩ <-> v = hd :: tl := by
  apply Iff.intro <;> intro h
  case _ =>
    unfold uncons at h
    injection h with e1 e2; subst e1 e2
    funext; case _ i =>
    induction i using Fin.induction generalizing v
    case zero => simp [head]
    case succ i ih => simp [tail]
  case _ => subst h; simp

def Vect.induction
  {A : Sort u1}
  {motive : (n : Nat) -> Vect n A -> Sort u2}
  (nil : motive 0 nil)
  (cons : {n : Nat} -> {tl : Vect n A} -> (hd : A) ->
    motive n tl -> motive (n + 1) (cons hd tl))
  : {n : Nat} -> (v : Vect n A) -> motive n v
| 0, v => by simp; exact nil
| n + 1, v => by {
  generalize zdef : uncons v = z
  obtain ⟨hd, tl⟩ := z
  replace cons := cons hd (induction nil cons tl)
  replace zdef := uncons_iff.1 zdef
  rw [zdef]; exact cons
}

@[simp]
theorem Vect.induction_nil : induction ni co nil = ni := by rfl

@[simp]
theorem Vect.induction_cons :
  induction ni co (hd :: tl) = co hd (induction ni co tl)
:= by
  simp [induction, uncons]; congr

def Vect.fold {A : Sort u1} (d : B) (f : A -> B -> B) {n : Nat} (v : Vect n A) : B :=
  induction (motive := λ _ _ => B) d f v

@[simp]
theorem Vect.fold_nil : fold d f nil = d := by rfl

@[simp]
theorem Vect.fold_cons : fold d f (hd :: tl) = f hd (fold d f tl) := by rfl

@[simp]
theorem Vect.map_id {v : Vect n A} : id <$> v = v := by rfl

theorem Vect.map_compose {v : Vect n A} :
  f <$> (g <$> v) = (f ∘ g) <$> v
:= by rfl
