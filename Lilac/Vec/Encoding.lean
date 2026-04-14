
import Lilac.Map

namespace Lilac.Fun

def Vec (A : Sort u) (n : Nat) := Fin n -> A

def Vec.nil : Vec A 0 := λ x => nomatch x

def Vec.cons (head : A) (tail : Vec A n) : Vec A (n + 1) :=
  Fin.cases (motive := λ _ => A) head tail

theorem Vec.cons_zero {tl : Vec A n} : (cons hd tl) 0 = hd := by simp [cons]

theorem Vec.cons_succ {tl : Vec A n} : (cons hd tl) i.succ = tl i := by simp [cons]

theorem Vec.eta0 {v : Vec A 0} : v = nil := by
  funext; case _ i =>
  apply Fin.elim0 i

def Vec.head (v : Vec A (n + 1)) : A := v 0

theorem Vec.head_cons : head (cons hd tl) = hd := by simp [head, cons]

def Vec.tail (v : Vec A (n + 1)) : Vec A n
| n => v (Fin.succ n)

theorem Vec.tail_cons : tail (cons hd tl) = tl := by
  simp [cons]; funext; case _ i => simp [tail]

def Vec.uncons (v : Vec A (n + 1)) : A ×' Vec A n := ⟨head v, tail v⟩

theorem Vec.uncons_cons : uncons (cons hd tl) = ⟨hd, tl⟩ := by
  simp [uncons, head_cons, tail_cons]

theorem Vec.uncons_iff : uncons v = ⟨hd, tl⟩ <-> v = cons hd tl := by
  apply Iff.intro <;> intro h
  case _ =>
    unfold uncons at h
    injection h with e1 e2; subst e1 e2
    funext; case _ i =>
    induction i using Fin.induction generalizing v
    case zero => simp [head, cons]
    case succ i ih => simp [tail, cons]
  case _ => subst h; simp [uncons_cons]

def Vec.induction
  {A : Sort u1}
  {motive : (n : Nat) -> Vec A n -> Sort u2}
  (nil : motive 0 nil)
  (cons : {n : Nat} -> (hd : A) -> {tl : Vec A n} ->
    motive n tl -> motive (n + 1) (cons hd tl))
  : {n : Nat} -> (v : Vec A n) -> motive n v
| 0, v => nil |> cast (by rw [<-eta0])
| n + 1, v => by {
  generalize zdef : uncons v = z
  obtain ⟨hd, tl⟩ := z
  replace cons := cons hd (induction nil cons tl)
  replace zdef := uncons_iff.1 zdef
  rw [zdef]; exact cons
}

theorem Vec.induction_nil : induction ni co nil = ni := by rfl

theorem Vec.induction_cons :
  induction ni co (cons hd tl) = co hd (induction ni co tl)
:= by
  simp [induction, uncons];
  have lem : (cons (cons hd tl).head (cons hd tl).tail) = cons hd tl := by
    unfold cons; unfold head; unfold tail
    rfl
  apply congrArg
  apply congrArg
  apply congrFun
  simp

theorem Vec.map_id {v : Vec A n} : id <$> v = v := by rfl

theorem Vec.map_compose {v : Vec A n} :
  f <$> (g <$> v) = (f ∘ g) <$> v
:= by rfl

end Lilac.Fun
