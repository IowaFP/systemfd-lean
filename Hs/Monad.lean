

abbrev DsM a := Except Std.Format a

namespace DsM

def ok : a -> DsM a := λ x => Except.ok x
def error : Std.Format -> DsM a := λ x => Except.error x
def bind : DsM a -> (a -> DsM b) -> DsM b := Except.bind

def toDsM (pfix : Std.Format) : Option a -> DsM a
| .some a => ok a
| .none => error (pfix ++ Std.Format.line)

def toDsMq : Option a -> DsM a := toDsM ""

def run [Repr a] : DsM a -> Std.Format
| .error e => "Error:" ++ Std.Format.line ++ e
| .ok t => repr t

end DsM

instance beq_DsMa [BEq a] : BEq (DsM a) where
     beq x y :=
       match (x, y) with
       | (.ok x, .ok y) => x == y
       | _ => False
