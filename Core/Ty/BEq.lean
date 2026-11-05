import Core.Ty.Definition

namespace Core

def Kind.beq : Kind -> Kind -> Bool
| base, base => true
| arrow A1 B1, arrow A2 B2 => Kind.beq A1 A2 && Kind.beq B1 B2
| _, _ => false


instance instBEq_Kind : BEq Kind where
  beq := Kind.beq


instance instReflBEq_Kind : ReflBEq Kind where
  rfl := by
    intro a; induction a <;> simp +instances [Kind.beq, instBEq_Kind] at *
    case _ ih1 ih2 =>
    constructor; apply ih1; apply ih2

instance instLawfulBeq_Kind : LawfulBEq Kind where
  eq_of_beq
  := by
    intro a b h
    induction a, b using Kind.beq.induct <;> simp +instances [instBEq_Kind, Kind.beq] at *
    case _ ih1 ih2 =>
      constructor
      · apply ih1 h.1
      · apply ih2 h.2

def Ty.beq : Ty -> Ty -> Bool
| var x, var y => x == y
| global x, global y => x == y
| arrow A1 B1, arrow A2 B2 => beq A1 A2 && beq B1 B2
| all K1 P1, all K2 P2 => K1 == K2 && beq P1 P2
| app A1 B1, app A2 B2 => beq A1 A2 && beq B1 B2
| eq K1 A1 B1, eq K2 A2 B2 => K1 == K2 && beq A1 A2 && beq B1 B2
| _, _ => false

instance instBEq_Ty : BEq Ty where
  beq := Ty.beq

instance instReflBEq_Ty : ReflBEq Ty where
  rfl := by
    intro a; induction a <;> simp +instances [instBEq_Ty, Ty.beq] at *
    all_goals (try case _ ih1 ih2 => constructor; assumption; assumption)
    case _ => assumption

instance instLawfulBEq_Ty : LawfulBEq Ty where
  eq_of_beq := by
    intro a b h
    induction a, b using Ty.beq.induct <;> simp +instances [instBEq_Ty, Ty.beq] at *
    assumption
    assumption
    all_goals (try
      case _ ih1 ih2 =>
      constructor
      · apply ih1 h.1
      · apply ih2 h.2)
    case _ ih =>
      constructor
      · apply h.1
      · apply ih h.2
    case _ ih1 ih2 =>
      constructor
      · apply h.1.1
      · constructor
        · apply ih1 h.1.2
        · apply ih2 h.2

instance instBEq_SpineTy : BEq SpineTy where
  beq := λ ⟨na, Ks1, nb, Ks2, nc, As, R⟩ ⟨na', Ks1', nb', Ks2', nc', As', R'⟩ =>
    na == na' && (Ks1.beq Ks1' && (nb == nb' && (Ks2.beq Ks2' && (nc == nc' && (As.beq As' && R == R')))))

instance : ReflBEq SpineTy where
  rfl
:= by
   intro a; rcases a with ⟨k1, Ks1, k2, Ks2, k3, Cs, R⟩
   simp [BEq.beq]; apply And.intro
   · apply Lilac.instReflBEqVec.rfl
   · apply And.intro
     · apply Lilac.instReflBEqVec.rfl
     · apply And.intro;
       · apply Lilac.instReflBEqVec.rfl
       · apply instReflBEq_Ty.rfl

instance : LawfulBEq SpineTy where
  eq_of_beq := by
    intro a b h
    rcases a with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
    rcases b with ⟨na', Ks1', nb', Ks2', nc', As', R'⟩
    simp [BEq.beq] at h;
    rcases h with ⟨e1, e2, e3, e4, e5, e6, e7⟩
    subst e1 e3 e5;
    simp; apply And.intro
    · apply Lilac.instLawfulBEqVec.eq_of_beq e2
    · apply And.intro
      · apply Lilac.instLawfulBEqVec.eq_of_beq e4
      · apply And.intro
        · apply Lilac.instLawfulBEqVec.eq_of_beq e6
        · apply instLawfulBEq_Ty.eq_of_beq e7


end Core
