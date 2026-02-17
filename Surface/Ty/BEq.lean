import Surface.Ty.Definition

def Surface.BaseKind.beq : Surface.BaseKind -> Surface.BaseKind -> Bool
| closed, closed => true
| .open, .open => true
| _, _ => false


instance Surface.instBEq_BaseKind : BEq BaseKind where
  beq := Surface.BaseKind.beq

@[simp]
instance Surface.instReflBEq_BaseKind : ReflBEq Surface.BaseKind where
  rfl := by
    intro a
    cases a
    all_goals (simp [Surface.instBEq_BaseKind, Surface.BaseKind.beq])

@[simp]
instance Surface.instLawfulBEq_BaseKind : LawfulBEq Surface.BaseKind where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b
    all_goals (simp at *)
    all_goals (simp [instBEq_BaseKind, BaseKind.beq] at h)

def Surface.Kind.beq : Kind -> Kind -> Bool
| base b1, base b2 => b1 == b2
| arrow A1 B1, arrow A2 B2 => Kind.beq A1 A2 && Kind.beq B1 B2
| _, _ => false


instance Surface.instBEq_Kind : BEq Kind where
  beq := Kind.beq


instance Surface.instReflBEq_Kind : ReflBEq Kind where
  rfl := by
    intro a; induction a <;> simp [Kind.beq, instBEq_Kind] at *
    case _ ih1 ih2 =>
    constructor; apply ih1; apply ih2

instance Surface.instLawfulBeq_Kind : LawfulBEq Kind where
  eq_of_beq := by
    intro a b h
    induction a, b using Kind.beq.induct <;> simp [instBEq_Kind, Kind.beq] at *
    apply h
    case _ ih1 ih2 =>
      constructor
      · apply ih1 h.1
      · apply ih2 h.2

def Surface.Ty.beq : Ty -> Ty -> Bool
| var x, var y => x == y
| global x, global y => x == y
| arrow A1 B1, arrow A2 B2 => beq A1 A2 && beq B1 B2
| all K1 P1, all K2 P2 => K1 == K2 && beq P1 P2
| app A1 B1, app A2 B2 => beq A1 A2 && beq B1 B2
| _, _ => false

instance Surface.instBEq_Ty : BEq Ty where
  beq := Ty.beq

instance Surface.instReflBEq_Type : ReflBEq Ty where
  rfl := by
    intro a; induction a <;> simp [instBEq_Ty, Ty.beq] at *
    all_goals (try case _ ih1 ih2 => constructor; assumption; assumption)
    case _ => assumption

instance Surface.instLawfulBeq_Ty : LawfulBEq Ty where
  eq_of_beq := by
    intro a b h
    induction a, b using Surface.Ty.beq.induct <;> simp [Surface.instBEq_Ty, Surface.Ty.beq] at *
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
