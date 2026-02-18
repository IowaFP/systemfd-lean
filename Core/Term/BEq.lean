import Core.Ty
import Core.Term.Definition

def Ctor0Variant.beq : Ctor0Variant -> Ctor0Variant -> Bool
| zero, zero => true
| refl A, refl B => A == B
| _, _ => false

instance instBEq_Ctor0Variant : BEq Ctor0Variant where
  beq := Ctor0Variant.beq

instance instReflBEq_Ctor0Variant : ReflBEq Ctor0Variant where
  rfl := by
    intro x; induction x <;> simp [instBEq_Ctor0Variant, Ctor0Variant.beq] at *

instance instLawfulBEq_CtorVariant : LawfulBEq Ctor0Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp [instBEq_Ctor0Variant, Ctor0Variant.beq] at *
    all_goals (induction b <;> simp at *)

def Ctor1Variant.beq : Ctor1Variant -> Ctor1Variant -> Bool
| sym, sym => true
| fst, fst => true
| snd, snd => true
| appt a, appt b => a == b
| _, _ => false

instance instBEq_Ctor1Variant : BEq Ctor1Variant where
  beq := Ctor1Variant.beq

instance instReflBEq_Ctor1Variant : ReflBEq Ctor1Variant where
  rfl := by
    intro x; induction x <;> simp [instBEq_Ctor1Variant, Ctor1Variant.beq] at *

instance instLawfulBEq_Ctor1Variant : LawfulBEq Ctor1Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp [instBEq_Ctor1Variant, Ctor1Variant.beq] at *
    all_goals (induction b <;> simp at *)


def Ctor2Variant.beq : Ctor2Variant -> Ctor2Variant -> Bool
| app b1, app b2 => b1 == b2
| cast, cast => true
| seq, seq => true
| appc, appc => true
| apptc, apptc => true
| arrowc, arrowc => true
| choice, choice => true
| _, _ => false

instance instBEq_Ctor2Variant : BEq Ctor2Variant where
  beq := Ctor2Variant.beq


instance instReflBEq_Ctor2Variant : ReflBEq Ctor2Variant where
  rfl := by
    intro x; induction x <;> simp [instBEq_Ctor2Variant, Ctor2Variant.beq] at *

instance instLawfulBEq_Ctor2Variant : LawfulBEq Ctor2Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp [instBEq_Ctor2Variant, Ctor2Variant.beq] at *
    all_goals (induction b <;> simp at *)

def TyBindVariant.beq : TyBindVariant -> TyBindVariant -> Bool
| lamt, lamt => true
| allc, allc => true
| _, _ => false

instance instBEq_TyBindVariant : BEq TyBindVariant where
  beq := TyBindVariant.beq

instance instReflBEq_TyBindVariant : ReflBEq TyBindVariant where
  rfl := by
    intro x; induction x <;> simp [instBEq_TyBindVariant, TyBindVariant.beq] at *

instance instLawfulBEq_TyBindVariant : LawfulBEq TyBindVariant where
  eq_of_beq := by
    intro x b; induction x <;> simp [instBEq_TyBindVariant, TyBindVariant.beq] at *
    all_goals (induction b <;> simp at *)


def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| global x, global y => x == y
| ctor0 c1, ctor0 c2 => c1 == c2
| ctor1 c1 a1, ctor1 c2 a2 => c1 == c2 && beq a1 a2
| ctor2 c1 a1 b1, ctor2 c2 a2 b2 => c1 == c2 && beq a1 a2 && beq b1 b2
| tbind A1 K1 t1, tbind A2 K2 t2 => A1 == A2 && K1 == K2 && beq t1 t2
| lam A1 t1, lam A2 t2 => A1 == A2 && beq t1 t2
| guard a1 b1 c1, guard a2 b2 c2 => beq a1 a2 && beq b1 b2 && beq c1 c2
| .match (n := n1) a1 b1 c1 d1, .match (n := n2) a2 b2 c2 d2 =>
  if h : n1 = n2 then
    let c : Vec Bool n1 := λ i => beq (c1 i) (c2 (by rw [h] at i; exact i))
    let p : Vec Bool n1 := λ i => beq (b1 i) (b2 (by rw[h] at i; exact i))
    beq a1 a2 && Vec.fold (·&&·) true c && Vec.fold (·&&·) true p && beq d1 d2
  else false
| _, _ => false

instance instBEq_Term : BEq Term where
  beq := Term.beq

instance instReflBEq_Term : ReflBEq Term where
  rfl := by
    intro a; induction a <;> simp [instBEq_Term, Term.beq] at *
    all_goals (repeat assumption)
    constructor; assumption; assumption
    constructor; constructor; assumption; assumption; assumption
    case «match» ih1 ih2 ih3 ih4 =>
    constructor
    · constructor
      · constructor; assumption;
        unfold Vec.fold;
        case _ n _ _ _ _ =>
        induction n
        case _ => simp
        case _ n ih v1 v2 =>         -- split
          simp;
        -- case _ => rfl
        -- case _ =>
        --   split; case _ h =>
        --   cases h; simp at *
        --   constructor
        --   apply ih3
          sorry
      · sorry
    · assumption

instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := by
    intro a b; cases a <;> simp [instBEq_Term] at *
    all_goals (induction b <;>
      simp [instBEq_Ctor0Variant, instBEq_Ctor1Variant, instBEq_Ctor2Variant, Term.beq] at *)
    case _ => intro e; apply eq_of_beq e
    case _ =>
      intro e1 e2;
      constructor
      apply eq_of_beq e1
      sorry
    sorry
    sorry
    sorry
    sorry
    sorry
