import Core.Ty
import Core.Term.Definition

def Ctor0Variant.beq : Ctor0Variant -> Ctor0Variant -> Bool
| zero, zero => true
| refl A, refl B => A == B
| _, _ => false

instance : BEq Ctor0Variant where
  beq := Ctor0Variant.beq

def Ctor1Variant.beq : Ctor1Variant -> Ctor1Variant -> Bool
| sym, sym => true
| fst, fst => true
| snd, snd => true
| appt a, appt b => a == b
| _, _ => false

instance : BEq Ctor1Variant where
  beq := Ctor1Variant.beq

def Ctor2Variant.beq : Ctor2Variant -> Ctor2Variant -> Bool
| app b1, app b2 => b1 == b2
| cast, cast => true
| seq, seq => true
| appc, appc => true
| apptc, apptc => true
| arrowc, arrowc => true
| choice, choice => true
| _, _ => false

instance : BEq Ctor2Variant where
  beq := Ctor2Variant.beq

def TyBindVariant.beq : TyBindVariant -> TyBindVariant -> Bool
| lamt, lamt => true
| allc, allc => true
| _, _ => false

instance : BEq TyBindVariant where
  beq := TyBindVariant.beq

def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| global x, global y => x == y
| ctor0 c1, ctor0 c2 => c1 == c2
| ctor1 c1 a1, ctor1 c2 a2 => c1 == c2 && beq a1 a2
| ctor2 c1 a1 b1, ctor2 c2 a2 b2 => c1 == c2 && beq a1 a2 && beq b1 b2
| tbind A1 K1 t1, tbind A2 K2 t2 => A1 == A2 && K1 == K2 && beq t1 t2
| lam b1 A1 t1, lam b2 A2 t2 => b1 == b2 && A1 == A2 && beq t1 t2
| guard a1 b1 c1, guard a2 b2 c2 => beq a1 a2 && beq b1 b2 && beq c1 c2
| .match (n := n1) a1 ps1 c1, .match (n := n2) a2 ps2 c2 =>
  if h : n1 = n2 then
    let c : Vec Bool n1 := λ i => beq (c1 i) (c2 (by rw [h] at i; exact i))
    let p : Vec Bool n1 := λ i => (ps1 i) == (ps2 (by rw[h] at i; exact i))
    beq a1 a2 && Vec.fold (·&&·) true c && Vec.fold (·&&·) true p
  else false
| _, _ => false

instance : BEq Term where
  beq := Term.beq
