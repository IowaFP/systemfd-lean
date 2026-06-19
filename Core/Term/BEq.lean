import Core.Ty
import Core.Term.Definition
import Core.Vec

open Lilac

namespace Core
def DataConst.beq : DataConst -> DataConst -> Bool
| .opn, .opn => true
| .cls, .cls => true
| _, _ => false

instance instBeq_DataConst : BEq DataConst where
  beq := DataConst.beq

def Ctor0Variant.beq : Ctor0Variant -> Ctor0Variant -> Bool
-- | fail, fail => true
| refl A, refl B => A == B
-- | _, _ => false

deriving instance BEq for SpCtorVariant

instance instBEq_Ctor0Variant : BEq Ctor0Variant where
  beq := Ctor0Variant.beq

instance instReflBEq_Ctor0Variant : ReflBEq Ctor0Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor0Variant, Ctor0Variant.beq] at *

instance instLawfulBEq_CtorVariant : LawfulBEq Ctor0Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor0Variant, Ctor0Variant.beq] at *
    all_goals (induction b <;> simp at *)

def Ctor1Variant.beq : Ctor1Variant -> Ctor1Variant -> Bool
| prj n1, prj n2 => n1 == n2
| appt a, appt b => a == b
| _, _ => false

instance instBEq_Ctor1Variant : BEq Ctor1Variant where
  beq := Ctor1Variant.beq

instance instReflBEq_Ctor1Variant : ReflBEq Ctor1Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor1Variant, Ctor1Variant.beq] at *

instance instLawfulBEq_Ctor1Variant : LawfulBEq Ctor1Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor1Variant, Ctor1Variant.beq] at *
    all_goals (induction b <;> simp at *)


def Ctor2Variant.beq : Ctor2Variant -> Ctor2Variant -> Bool
| app, app => true
| apptc, apptc => true
| _, _ => false

instance instBEq_Ctor2Variant : BEq Ctor2Variant where
  beq := Ctor2Variant.beq


instance instReflBEq_Ctor2Variant : ReflBEq Ctor2Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor2Variant, Ctor2Variant.beq] at *

instance instLawfulBEq_Ctor2Variant : LawfulBEq Ctor2Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor2Variant, Ctor2Variant.beq] at *
    all_goals (induction b <;> simp at *)

def TyBindVariant.beq : TyBindVariant -> TyBindVariant -> Bool
| lamt, lamt => true
| allc, allc => true
| _, _ => false

instance instBEq_TyBindVariant : BEq TyBindVariant where
  beq := TyBindVariant.beq

instance instReflBEq_TyBindVariant : ReflBEq TyBindVariant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_TyBindVariant, TyBindVariant.beq] at *

instance instLawfulBEq_TyBindVariant : LawfulBEq TyBindVariant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_TyBindVariant, TyBindVariant.beq] at *
    all_goals (induction b <;> simp at *)

def Pattern.eq : Pattern m1 -> Pattern m2 -> Bool
| .nil, .nil => true
| .cons (x1, ⟨n1, v1, k1⟩) xs, .cons (x2, ⟨n2, v2, k2⟩) ys =>
  if n1 == n2 && k1 == k2 && x1 == x2
  then let v1' : Lilac.Vec Ty n1 := v1.to
       let v2' : Lilac.Vec Ty n2 := v2.to
       Pattern.eq xs ys && Lilac.Vec.beq v1' v2'
  else false
| _, _ => false

def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| defn x, defn y => x == y
| ctor0 c1, ctor0 c2 => c1 == c2
| ctor1 c1 a1, ctor1 c2 a2 => c1 == c2 && beq a1 a2
| ctor2 c1 a1 b1, ctor2 c2 a2 b2 => c1 == c2 && beq a1 a2 && beq b1 b2
| tbind A1 K1 t1, tbind A2 K2 t2 => A1 == A2 && K1 == K2 && beq t1 t2
| lam A1 t1, lam A2 t2 => A1 == A2 && beq t1 t2
| .cast A a1 a2, .cast B b1 b2 => A == B && beq a1 b1 && beq a2 b2
| .mtch m1 n1 a1 b1 c1, .mtch m2 n2 a2 b2 c2 =>
  if h : n1 == n2 && m1 == m2 then
    let a : Lilac.Fun.Vec Bool m1 := λ i => beq (a1 i) (a2 (by simp at h; rw [h.2] at i; exact i))
    let c : Lilac.Fun.Vec Bool n1 := λ i => beq (c1 i) (c2 (by simp at h; rw [h.1] at i; exact i))
    let p : Lilac.Fun.Vec Bool n1 := λ i =>
      let p1 : Pattern m1 := (b1 i).to
      let p2 : Pattern m2 := (b2 (by simp at h; rw[h.1] at i; exact i)).to
      Pattern.eq p1 p2
    Vec.foldl (·&&·) true a.to && Vec.foldl (·&&·) true c.to && Vec.foldl (·&&·) true p.to
  else false
| .spctor (n := n1) v1 s1 A1 B1 ts1, .spctor (n := n2) v2 s2 A2 B2 ts2 =>
  if h : n1 == n2
  then
    let bs : Lilac.Fun.Vec Bool n1 := (λ i => beq (ts1 i) (ts2 (by simp at h; rw[h] at i; exact i)))
    v1 == v2 && s1 == s2 && A1.beq A2 && B1.beq B2 && Vec.foldl (·&&·) true bs.to
  else false
| _, _ => false

instance instBEq_Term : BEq Term where
  beq := Term.beq

instance instReflBEq_Term : ReflBEq Term where
  rfl := by sorry
    -- intro a; induction a <;> simp [instBEq_Term, Term.beq] at *
    -- all_goals (repeat assumption)
    -- constructor; assumption; assumption
    -- constructor; constructor; assumption; assumption; assumption
    -- case «match» ih1 ih2 ih3 ih4 =>
    -- constructor
    -- · constructor
    --   · constructor; assumption;
    --     unfold Vect.fold;
    --     case _ n _ _ _ _ =>
    --     induction n
    --     case _ => simp
    --     case _ n ih v1 v2 =>

    --       -- split
    --       -- simp;
    --     -- case _ => rfl
    --     -- case _ =>
    --     --   split; case _ h =>
    --     --   cases h; simp at *
    --     --   constructor
    --     --   apply ih3
    --       sorry
    --   · sorry
    -- · assumption

instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := by sorry
    -- intro a b; cases a <;> simp [instBEq_Term] at *
    -- all_goals (induction b <;>
    --   simp [instBEq_Ctor0Variant, instBEq_Ctor1Variant, instBEq_Ctor2Variant, Term.beq] at *)
    -- case _ => intro e; apply eq_of_beq e
    -- case _ =>
    --   intro e1 e2;
    --   constructor
    --   apply eq_of_beq e1
    --   sorry
    -- sorry
    -- sorry
    -- sorry
    -- sorry
    -- sorry
end Core
