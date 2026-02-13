
import Lilac.Map
import Lilac.Vect.Definition
import Lilac.Vect.List

theorem Fin.unfold_ofNat1 : 1 = @Fin.succ (n + 1) 0 := by simp
theorem Fin.unfold_ofNat2 : 2 = @Fin.succ (n + 2) (@Fin.succ (n + 1) 0) := by simp

def Fin.cases1
  {motive : Fin 1 -> Sort u}
  (h : motive 0)
  (v : Fin 1) : motive v
:= by
  induction v using Fin.induction
  case _ => apply h
  case _ i _ => apply Fin.elim0 i

def Fin.cases2
  {motive : Fin 2 -> Sort u}
  (h1 : motive 0) (h2 : motive 1)
  (v : Fin 2) : motive v
:= by
  induction v using Fin.induction
  case _ => apply h1
  case _ i h => cases i using Fin.cases1; apply h2

def Fin.cases3
  {motive : Fin 3 -> Sort u}
  (h1 : motive 0) (h2 : motive 1) (h3 : motive 2)
  (v : Fin 3) : motive v
:= by
  induction v using Fin.induction
  case _ => apply h1
  case _ i h =>
    cases i using Fin.cases2
    apply h2; apply h3

@[simp]
theorem Vect.eta1 (t : Vect 1 T) : ↑[t 0] = t := by
  funext; case _ i =>
  cases i using Fin.cases1; simp

@[simp]
theorem Vect.eta2 (t : Vect 2 T) : ↑[t 0, t 1] = t := by
  funext; case _ i =>
  cases i using Fin.cases2 <;> simp [cons]
  rw [Fin.unfold_ofNat1, Fin.cases_succ]; simp

@[simp]
theorem Vect.eta3 (t : Vect 3 T) : ↑[t 0, t 1, t 2] = t := by
  funext; case _ i =>
  cases i using Fin.cases3 <;> simp [cons]
  rw [Fin.unfold_ofNat1, Fin.cases_succ]; simp
  rw [Fin.unfold_ofNat2, Fin.cases_succ, Fin.cases_succ]; simp

@[simp]
theorem Vect.inv1 {a b : Vect 1 T} : a = b <-> a 0 = b 0 := by
  apply Iff.intro; intro h; subst h; rfl
  intro h; funext; case _ i =>
  cases i using Fin.cases1; exact h

@[simp]
theorem Vect.inv2 {a b : Vect 2 T} : a = b <-> a 0 = b 0 ∧ a 1 = b 1 := by
  apply Iff.intro; intro h; subst h; simp
  intro h; funext; case _ i =>
  cases i using Fin.cases2 <;> simp [*]

@[simp]
theorem Vect.inv3 {a b : Vect 3 T} : a = b <-> a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 := by
  apply Iff.intro; intro h; subst h; simp
  intro h; funext; case _ i =>
  cases i using Fin.cases3 <;> simp [*]
