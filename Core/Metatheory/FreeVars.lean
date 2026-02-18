import LeanSubst
import Core.Typing

open LeanSubst

inductive Ty.FV : Ty -> Nat -> Prop where
| var : FV t#x x
| arrowr : FV a x -> FV (a -:> b) x
| arrowl : FV b x -> FV (a -:> b) x
| eqr : FV a x -> FV (a ~[K]~ b) x
| eql : FV b x -> FV (a ~[K]~ b) x
| appr : FV a x -> FV (a • b) x
| appl : FV b x -> FV (a • b) x
| all : FV p (a + 1) -> FV (∀[K] p) a


instance instMembership_Nat_Ty : Membership Nat Ty where
  mem := Ty.FV


@[simp]
def iterate (f : T -> T) : Nat -> T -> T
| 0 => λ x => x
| n + 1 => λ x => f $ (iterate f n) x

notation f "^[" n "]" => iterate f n

@[simp]
theorem iterate_succ {x : Nat} : ((· + 1)^[n]) x = x + n := by
  induction n <;> simp at *
  case succ n ih => rw [ih]; omega


theorem lift_iterated_succ_is_re :
   ((Subst.lift (T := Ty))^[n]) +1 y = z ->
   ∃ i, z = re i := by
intro h
induction n generalizing y z <;> simp at *
case zero => exists y + 1; symm at h; assumption
case succ n ih =>
  cases y <;> simp at *
  case zero => exists 0; symm at h; assumption
  case succ y =>
    simp [Subst.compose] at *
    rcases ih with ⟨k, ih⟩
    generalize zdef : (((Subst.lift (T := Ty))^[n]) +1) y = z at *
    cases z <;> simp at *
    case _ a => exists (a + 1); symm at h; assumption

-- x ∉ T[(x + 1)]
theorem FV.var_not_in_one_more {T : Ty} : (x ∉ T[((Subst.lift)^[x]) +1:Ty]) := by
intro h
induction T generalizing x <;> simp at *
case var y =>
  induction x generalizing y <;> simp at *
  case zero => cases h
  case succ n ih =>
  simp [Subst.compose] at *
  cases y <;> simp at *
  case zero => cases h
  case succ y =>
  replace ih := ih y
  generalize zdef : (((Subst.lift (T := Ty))^[n]) +1 y) = z at *
  have lem := lift_iterated_succ_is_re zdef
  rcases lem with ⟨k , lem⟩
  subst z; rw[lem] at h; simp at h
  cases h; apply ih; rw[lem]; simp; apply Ty.FV.var
case all P ih =>
  cases h; case _ h =>
  apply @ih (x + 1); simp; apply h
case global => cases h
all_goals (
case _ ih1 ih2 =>
  replace ih1 := @ih1 x
  replace ih2 := @ih2 x
  cases h <;> simp at *
  case _ h => apply ih1 h
  case _ h => apply ih2 h)


theorem FV.zero_not_in_succ {T : Ty} : 0 ∉ T[+1] := by
have lem := @FV.var_not_in_one_more (T := T) 0
simp at lem; apply lem
