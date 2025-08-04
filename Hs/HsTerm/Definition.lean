
inductive HsCtor2Variant : Type where
| arrowk -- a -k> b
| appk   -- a `•k b
| app    -- a `• b
| appt    -- a `•t b

inductive HsBind2Variant : Type where
| all   -- ∀[A] B
| arrow -- a → b
| farrow -- a ⇒ b
| lam   -- `λ B
| lamt -- `Λ B

-- Surface syntax terms
inductive HsTerm : Type where
| HsType : HsTerm -- ★
| HsKind : HsTerm -- "□"
| HsVar : Nat -> HsTerm
| HsName : String -> HsTerm
| HsHole : HsTerm -> HsTerm
| HsAnnotate : HsTerm -> HsTerm -> HsTerm
| HsCtor2 : HsCtor2Variant -> HsTerm -> HsTerm -> HsTerm
| HsBind2 : HsBind2Variant -> HsTerm -> HsTerm -> HsTerm
| HsLet :           HsTerm -> HsTerm -> HsTerm -> HsTerm
| HsIte : HsTerm -> HsTerm -> HsTerm -> HsTerm -> HsTerm

protected def HsTerm.repr : (a : HsTerm) -> (p : Nat) -> Std.Format
| HsType, _ => "`★"
| HsKind, _ => "`□"
| HsVar n , _ => "`#" ++ Nat.repr n
| HsName n , _ => n
| HsHole n , p => "__@" ++ Std.Format.paren (HsTerm.repr n p)
| HsAnnotate A t, p => Std.Format.paren ((HsTerm.repr t max_prec) ++ " : " ++ (HsTerm.repr A p))
| HsCtor2 .arrowk a b, p => Repr.addAppParen ((HsTerm.repr a max_prec) ++ " `-k> " ++ (HsTerm.repr b p)) p

| HsCtor2 .appk a b, p => Repr.addAppParen ((HsTerm.repr a max_prec) ++ " `•k " ++ (HsTerm.repr b max_prec)) p
| HsCtor2 .app a b, p => Repr.addAppParen ((HsTerm.repr a max_prec) ++ " `• " ++ (HsTerm.repr b max_prec)) p
| HsCtor2 .appt a b, p => Repr.addAppParen ((HsTerm.repr a max_prec) ++ " `•t " ++ (HsTerm.repr b max_prec)) p

| HsBind2 .lam t1 t2, p => "`λ" ++ Std.Format.sbracket (HsTerm.repr t1 p)  ++  HsTerm.repr t2 p
| HsBind2 .lamt t1 t2, p => "`Λ" ++ Std.Format.sbracket (HsTerm.repr t1 p)  ++ HsTerm.repr t2 p
| HsBind2 .all t1 t2 , p => "`∀" ++ Std.Format.sbracket (HsTerm.repr t1 p) ++ HsTerm.repr t2 p
| HsBind2 .arrow t1 t2 , p => Repr.addAppParen ((HsTerm.repr t1 max_prec) ++ " → " ++ HsTerm.repr t2 p) p
| HsBind2 .farrow t1 t2 , p => Repr.addAppParen ((HsTerm.repr t1 max_prec) ++ " ⇒ " ++ HsTerm.repr t2 p) p
| HsLet t1 t2 t3 , p =>
  "HsLet (" ++ HsTerm.repr t1 p ++ ":" ++ HsTerm.repr t2 p ++ ") In"
  ++ Std.Format.line ++ HsTerm.repr t3 p
| HsIte t1 t2 t3 t4, p => Std.Format.nest 4 <|
  " HsIf " ++ HsTerm.repr t1 p ++ " ← " ++ HsTerm.repr t2 p ++ Std.Format.line ++
  " Then " ++ HsTerm.repr t3 p ++ Std.Format.line ++
  " Else " ++ Std.Format.line ++ HsTerm.repr t4 p

instance HsTerm_repr : Repr HsTerm where
  reprPrec a p := HsTerm.repr a p

notation "`★" => HsTerm.HsType
notation "`□" => HsTerm.HsKind
infixl:15 " `• " => HsTerm.HsCtor2 HsCtor2Variant.app
infixl:15 " `•k " => HsTerm.HsCtor2 HsCtor2Variant.appk
infixl:15 " `•t " => HsTerm.HsCtor2 HsCtor2Variant.appt
notation:15  a " `-k> " b => HsTerm.HsCtor2 HsCtor2Variant.arrowk a b
notation:15 "λ̈[" a "]" b => HsTerm.HsBind2 HsBind2Variant.lam a b
notation:15 "Λ̈[" a "]" b => HsTerm.HsBind2 HsBind2Variant.lamt a b
notation:15 "`∀{" a "}" b => HsTerm.HsBind2 HsBind2Variant.all a b
notation:15  a " → " b => HsTerm.HsBind2 HsBind2Variant.arrow a b
notation:15  a " ⇒ " b => HsTerm.HsBind2 HsBind2Variant.farrow a b
prefix:max "`#" => HsTerm.HsVar
notation:15 "HsIf " p " ← " s " Then " i " Else " e => HsTerm.HsIte p s i e
prefix:max "__@" => HsTerm.HsHole


namespace HsTerm
 @[simp]
 def size : HsTerm -> Nat
 | HsType => 0
 | HsKind => 0
 | HsVar _ => 0
 | HsName _ => 0
 | HsHole t1 => size t1 + 1
 | HsAnnotate t1 t2 => size t1 + size t2 + 1
 | HsCtor2 _ t1 t2 => size t1 + size t2 + 1
 | HsBind2 _ t1 t2 => size t1 + size t2 + 1
 | HsLet t1 t2 t3 => size t1 + size t2 + size t3 + 1
 | HsIte t1 t2 t3 t4 => size t1 + size t2 + size t3 + size t4 + 1
end HsTerm

instance sizeOf_HsTerm : SizeOf HsTerm where
  sizeOf := HsTerm.size

namespace HsCtor2Variant
  @[simp]
  def beq : HsCtor2Variant -> HsCtor2Variant -> Bool
  | arrowk, arrowk => true
  | appk, appk => true
  | app, app => true
  | appt, appt => true
  | _, _ => false
end HsCtor2Variant

@[simp]
instance instBEq_HsCtor2Variant : BEq HsCtor2Variant where
  beq := HsCtor2Variant.beq

instance instLawfulBEq_HsCtor2Variant : LawfulBEq HsCtor2Variant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace HsBind2Variant
  @[simp]
  def beq : HsBind2Variant -> HsBind2Variant -> Bool
  | all, all => true
  | arrow, arrow => true
  | farrow, farrow => true
  | lam, lam => true
  | lamt, lamt => true
  | _, _ => false
end HsBind2Variant

@[simp]
instance instBEq_HsBind2Variant : BEq HsBind2Variant where
  beq := HsBind2Variant.beq

instance instLawfulBEq_HsBind2Variant : LawfulBEq HsBind2Variant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace HsTerm
  @[simp]
  def beq : HsTerm -> HsTerm -> Bool
  | HsKind, HsKind => true
  | HsType, HsType => true
  | HsVar x, HsVar y => x == y
  | HsName x, HsName y => x == y
  | HsHole x, HsHole y => beq x y
  | HsAnnotate x1 x2, HsAnnotate y1 y2 => beq x1 y1 && beq x2 y2
  | HsIte x1 x2 x3 x4, HsIte y1 y2 y3 y4 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4
  | HsLet x1 x2 x3, HsLet y1 y2 y3 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3
  | HsCtor2 v1 x1 x2, HsCtor2 v2 y1 y2 =>
    v1 == v2 && beq x1 y1 && beq x2 y2
  | HsBind2 v1 x1 x2, HsBind2 v2 y1 y2 =>
    v1 == v2 && beq x1 y1 && beq x2 y2
  | _, _ => false

  theorem eq_of_beq : HsTerm.beq a b = true -> a = b := by
  intro h
  induction a generalizing b
  case HsName =>
    cases b
    case HsName =>
      simp at *; assumption
    all_goals (simp at *)
  case HsHole ih =>
    cases b
    case HsHole =>
      simp at *; rw[ih h]
    all_goals (simp at *)
  case HsAnnotate ih1 ih2 =>
    cases b
    case HsAnnotate =>
      simp at *; rw [ih1 h.1, ih2 h.2]; simp
    all_goals (simp at *)
  case HsCtor2 v1 x1 x2 ih1 ih2 =>
    cases b
    case HsCtor2 v2 y1 y2 =>
      have lem := @LawfulBEq.eq_of_beq HsCtor2Variant _ _ v1 v2
      simp at *; replace lem := lem h.1.1
      rw [lem, ih1 h.1.2, ih2 h.2]; simp
    all_goals (simp at *)
  case HsBind2 v1 x1 x2 ih1 ih2 =>
    cases b
    case HsBind2 v2 y1 y2 =>
      have lem := @LawfulBEq.eq_of_beq HsBind2Variant _ _ v1 v2
      simp at *; replace lem := lem h.1.1
      rw [lem, ih1 h.1.2, ih2 h.2]; simp
    all_goals (simp at *)
  any_goals (cases b <;> simp at *)
  case _ => simp [*]
  case _ ih1 ih2 ih3 _ _ _ =>
    rw[ih1 h.1.1, ih2 h.1.2, ih3 h.2]
    simp
  case _ ih1 ih2 ih3 ih4 _ _ _ _ =>
    rw [ih1 h.1.1.1, ih2 h.1.1.2]
    rw [ih3 h.1.2, ih4 h.2]; simp

  theorem rfl : HsTerm.beq a a = true := by
  induction a <;> simp at * <;> simp [*]

end HsTerm

@[simp]
instance instBEq_HsTerm : BEq HsTerm where
  beq := HsTerm.beq

instance instLawfulBEq_HsTerm : LawfulBEq HsTerm where
  eq_of_beq := HsTerm.eq_of_beq
  rfl := HsTerm.rfl
