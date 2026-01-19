import Core.Ty.Definition

def BaseKind.beq : BaseKind -> BaseKind -> Bool
| closed, closed => true
| .open, .open => true
| _, _ => false

instance : BEq BaseKind where
  beq := BaseKind.beq

def Kind.beq : Kind -> Kind -> Bool
| base b1, base b2 => b1 == b2
| arrow A1 B1, arrow A2 B2 => beq A1 A2 && beq B1 B2
| _, _ => false

instance : BEq Kind where
  beq := Kind.beq

def Ty.beq : Ty -> Ty -> Bool
| var x, var y => x == y
| global x, global y => x == y
| arrow b1 A1 B1, arrow b2 A2 B2 => b1 == b2 && beq A1 A2 && beq B1 B2
| all K1 P1, all K2 P2 => K1 == K2 && beq P1 P2
| app A1 B1, app A2 B2 => beq A1 A2 && beq B1 B2
| eq K1 A1 B1, eq K2 A2 B2 => K1 == K2 && beq A1 A2 && beq B1 B2
| _, _ => false

instance : BEq Ty where
  beq := Ty.beq
