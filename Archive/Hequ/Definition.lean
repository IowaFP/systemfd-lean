
import Lilac.Sequ.Definition

namespace Lilac.Fun

def Hequ (A : Sequ (Sort u)) := (i : Nat) -> A i

def Hequ.cons (head : A) (tail : Hequ T) : Hequ (A::T)
| 0 => head
| n + 1 => tail n

infixr:67 (name := hequ_cons) " ::: " => Hequ.cons

end Lilac.Fun
