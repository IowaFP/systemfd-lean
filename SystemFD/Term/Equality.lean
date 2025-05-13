import SystemFD.Term.Definition

namespace Ctor1Variant
  @[simp]
  def beq : Ctor1Variant -> Ctor1Variant -> Bool
  | sym, sym => true
  | fst, fst => true
  | snd, snd => true
  | _, _ => false
end Ctor1Variant

@[simp]
instance instBEq_Ctor1Variant : BEq Ctor1Variant where
  beq := Ctor1Variant.beq

instance instLawfulBEq_Ctor1Variant : LawfulBEq Ctor1Variant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace Ctor2Variant
  @[simp]
  def beq : Ctor2Variant -> Ctor2Variant -> Bool
  | refl, refl => true
  | arrowk, arrowk => true
  | appk, appk => true
  | appt, appt => true
  | app, app => true
  | cast, cast => true
  | seq, seq => true
  | appc, appc => true
  | apptc, apptc => true
  | choice, choice => true
  | _, _ => false
end Ctor2Variant

@[simp]
instance instBEq_Ctor2Variant : BEq Ctor2Variant where
  beq := Ctor2Variant.beq

instance instLawfulBEq_Ctor2Variant : LawfulBEq Ctor2Variant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace Bind2Variant
  @[simp]
  def beq : Bind2Variant -> Bind2Variant -> Bool
  | all, all => true
  | lamt, lamt => true
  | lam, lam => true
  | arrow, arrow => true
  | allc, allc => true
  | arrowc, arrowc => true
  | _, _ => false
end Bind2Variant

@[simp]
instance instBEq_Bind2Variant : BEq Bind2Variant where
  beq := Bind2Variant.beq

instance instLawfulBEq_Bind2Variant : LawfulBEq Bind2Variant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace Term
  @[simp]
  def beq : Term -> Term -> Bool
  | kind, kind => true
  | type, type => true
  | zero, zero => true
  | var x, var y => x == y
  | eq x1 x2 x3, eq y1 y2 y3 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3
  | ite x1 x2 x3 x4, ite y1 y2 y3 y4 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4
  | guard x1 x2 x3, guard y1 y2 y3 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3
  | letterm x1 x2 x3, letterm y1 y2 y3 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3
  | ctor1 v1 x1, ctor1 v2 x2 =>
    v1 == v2 && beq x1 x2
  | ctor2 v1 x1 x2, ctor2 v2 y1 y2 =>
    v1 == v2 && beq x1 y1 && beq x2 y2
  | bind2 v1 x1 x2, bind2 v2 y1 y2 =>
    v1 == v2 && beq x1 y1 && beq x2 y2
  | _, _ => false

  theorem eq_of_beq : Term.beq a b = true -> a = b := by
  intro h
  induction a generalizing b
  case ctor1 v1 x1 ih =>
    cases b
    case ctor1 v2 x2 =>
      have lem := @LawfulBEq.eq_of_beq Ctor1Variant _ _ v1 v2
      simp at *; replace lem := lem h.1
      rw [lem, ih h.2]; simp
    all_goals (simp at *)
  case ctor2 v1 x1 x2 ih1 ih2 =>
    cases b
    case ctor2 v2 y1 y2 =>
      have lem := @LawfulBEq.eq_of_beq Ctor2Variant _ _ v1 v2
      simp at *; replace lem := lem h.1.1
      rw [lem, ih1 h.1.2, ih2 h.2]; simp
    all_goals (simp at *)
  case bind2 v1 x1 x2 ih1 ih2 =>
    cases b
    case bind2 v2 y1 y2 =>
      have lem := @LawfulBEq.eq_of_beq Bind2Variant _ _ v1 v2
      simp at *; replace lem := lem h.1.1
      rw [lem, ih1 h.1.2, ih2 h.2]; simp
    all_goals (simp at *)
  any_goals (cases b <;> simp at *)
  case _ => simp [*]
  case _ ih1 ih2 ih3 _ _ _ =>
    rw [ih1 h.1.1, ih2 h.1.2]
    rw [ih3 h.2]; simp
  case _ ih1 ih2 ih3 ih4 _ _ _ _ =>
    rw [ih1 h.1.1.1, ih2 h.1.1.2]
    rw [ih3 h.1.2, ih4 h.2]; simp
  case _ ih1 ih2 ih3 _ _ _ =>
    rw [ih1 h.1.1, ih2 h.1.2]
    rw [ih3 h.2]; simp
  case _ ih1 ih2 ih3 _ _ _ =>
    rw [ih1 h.1.1, ih2 h.1.2]
    rw [ih3 h.2]; simp

  theorem rfl : Term.beq a a = true := by
  induction a <;> simp at * <;> simp [*]

end Term

@[simp]
instance instBEq_Term : BEq Term where
  beq := Term.beq

instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := Term.eq_of_beq
  rfl := Term.rfl
