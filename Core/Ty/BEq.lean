import Core.Ty.Definition

@[simp]
def BaseKind.beq : BaseKind -> BaseKind -> Bool
| closed, closed => true
| .open, .open => true
| _, _ => false

@[simp]
instance : BEq BaseKind where
  beq := BaseKind.beq

@[simp]
instance instReflBEq_BaseKind : ReflBEq BaseKind where
  rfl := by
    intro a
    cases a
    all_goals (unfold BEq.beq; unfold instBEqBaseKind; simp)

@[simp]
instance instLawfulBEq_BaseKind : LawfulBEq BaseKind where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b
    all_goals (simp at *)
    all_goals (unfold BEq.beq at h;  unfold instBEqBaseKind at h; simp at h)

@[simp]
def Kind.beq : Kind -> Kind -> Bool
| base b1, base b2 => b1 == b2
| arrow A1 B1, arrow A2 B2 => Kind.beq A1 A2 && Kind.beq B1 B2
| _, _ => false

@[simp]
instance : BEq Kind where
  beq := Kind.beq

@[simp]
instance instReflBEq_Kind : ReflBEq Kind where
  rfl := by
    intro a; induction a
    all_goals (unfold BEq.beq; unfold instBEqKind; simp)
    case _ ih1 ih2 =>
    constructor; apply ih1; apply ih2

@[simp]
instance instLawfulBeq_Kind : LawfulBEq Kind where
  eq_of_beq := by
    intro a b h
    induction a, b using Kind.beq.induct <;> simp at *
    apply eq_of_beq h
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

instance instReflBEq_Type : ReflBEq Ty where
  rfl := by
    intro a; induction a <;> simp [instBEq_Ty, Ty.beq] at *
    all_goals (try case _ ih1 ih2 => constructor; assumption; assumption)
    case _ => assumption

instance instLawfulBeq_Ty : LawfulBEq Ty where
  eq_of_beq := by
    intro a b h
    induction a, b using Ty.beq.induct <;> simp [instBEq_Ty, Ty.beq] at *
    assumption
    assumption
    all_goals (try
      case _ ih1 ih2 =>
      constructor
      · apply ih1 h.1
      · apply ih2 h.2)
    case _ ih =>
      constructor
      · apply eq_of_beq h.1
      · apply ih h.2
    case _ ih1 ih2 =>
      constructor
      · apply eq_of_beq h.1.1
      · constructor
        · apply ih1 h.1.2
        · apply ih2 h.2
