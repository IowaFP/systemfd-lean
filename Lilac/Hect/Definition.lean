
import Lilac.Vect.Definition

def Hect (n : Nat) (A : Vect n (Sort u)) := (i : Fin n) -> A i

def Hect.nil : Hect 0 A := λ x => nomatch x

def Hect.cons (head : A) (tail : Hect n T) : Hect (n + 1) (A::T) :=
  Fin.cases (motive := A::T) head tail

infixr:67 (name := hect_cons) " ::: " => Hect.cons

@[simp]
theorem Hect.cons_zero {tl : Hect n A} : (hd ::: tl) 0 = hd := by simp [cons]

@[simp]
theorem Hect.cons_succ {tl : Hect n A} : (hd ::: tl) i.succ = tl i := by simp [cons]

@[simp]
theorem Hect.eta0 {v : Hect 0 A} : v = nil := by
  funext; case _ i =>
  apply Fin.elim0 i

def Hect.head (v : Hect (n + 1) (T::A)) : T := v 0

@[simp]
theorem Hect.head_cons : head (hd ::: tl) = hd := by simp [head, cons]

def Hect.tail (v : Hect (n + 1) (T::A)) : Hect n A
| n => v (Fin.succ n)

@[simp]
theorem Hect.tail_cons : tail (hd ::: tl) = tl := by
  simp [cons]; funext; case _ i => simp [tail]

def Hect.uncons (v : Hect (n + 1) (T::A)) : T ×' Hect n A := ⟨head v, tail v⟩

@[simp]
theorem Hect.uncons_cons : uncons (hd ::: tl) = ⟨hd, tl⟩ := by simp [uncons]

theorem Hect.uncons_iff : uncons v = ⟨hd, tl⟩ <-> v = hd ::: tl := by
  apply Iff.intro <;> intro h
  case _ =>
    unfold uncons at h
    injection h with e1 e2; subst e1 e2
    funext; case _ i =>
    induction i using Fin.induction generalizing v
    case zero => simp [head]
    case succ i ih => simp [tail]
  case _ => subst h; simp

def Hect.induction
  {motive : (n : Nat) -> (A : Vect n (Sort u1)) -> Hect n A -> Sort u2}
  (nil : motive 0 .nil nil)
  (cons : {T : Sort u1} -> {n : Nat} -> {A : Vect n (Sort u1)} ->
    (hd : T) -> {tl : Hect n A} ->
    motive n A tl -> motive (n + 1) (T::A) (cons hd tl))
  : {n : Nat} -> {A : Vect n (Sort u1)} -> (v : Hect n A) -> motive n A v
| 0, A, v => by simp; rw [Vect.eta0 (v := A)]; exact nil
| n + 1, A, v => by {
  generalize Udef : A.uncons = U
  obtain ⟨T, A'⟩ := U
  replace Udef := Vect.uncons_iff.1 Udef
  subst Udef
  generalize zdef : uncons v = z
  obtain ⟨hd, tl⟩ := z
  replace cons := cons hd (induction nil cons tl)
  replace zdef := uncons_iff.1 zdef
  rw [zdef]; exact cons
}

@[simp]
theorem Hect.induction_nil : induction ni co nil = ni := by rfl

@[simp]
theorem Hect.induction_cons :
  induction ni co (hd ::: tl) = co hd (induction ni co tl)
:= by
  simp [induction, uncons]; congr
