
def Sequ (A : Sort u) := Nat -> A

def Sequ.cons (head : A) (tail : Sequ A) : Sequ A
| 0 => head
| n + 1 => tail n

infixr:67 " :: " => Sequ.cons
