
import Init.Control.Lawful

abbrev DsM a := Except Std.Format a

namespace DsM

@[simp]
def ok : a -> DsM a := λ x => Except.ok x

@[simp]
def error : Std.Format -> DsM a := λ x => Except.error x

@[simp]
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

@[simp, grind]
instance instBind_DsM : Bind DsM where bind := Except.bind

@[simp, grind]
instance instPure_DsM : Pure DsM where pure := Except.pure

@[simp, grind]
instance instFunctor_DsM : Functor DsM where map := Except.map

@[simp, grind]
instance instMonad_DsM : Monad DsM := Except.instMonad

@[simp, grind] instance LawFulFunctor_DsM : LawfulFunctor DsM := instLawfulFunctorExcept
@[simp, grind] instance LawFulApplicative_DsM : LawfulApplicative DsM := instLawfulApplicativeExcept
@[simp, grind] instance LawFulMonad_DsM : LawfulMonad DsM := instLawfulMonadExcept

namespace DsM

@[simp, grind]
theorem bind_eq_ok (f : α -> DsM β) (b : β) (x : DsM α):
  DsM.bind x f = .ok b ↔ ∃ (a : α), (x = .ok a) ∧ f a = .ok b := by
cases x <;> simp at *
· intro; case _ j1 j2 =>
  unfold Except.bind at j2; simp at j2
· unfold Except.bind; simp

end DsM

namespace Except

@[simp, grind]
theorem bind_eq_ok (f : α -> Except ε β) (b : β) (x : Except ε α):
  Except.bind x f = .ok b ↔ ∃ (a : α), (x = .ok a) ∧ f a = .ok b := by
cases x <;> simp at *
· intro; case _ j1 j2 =>
  unfold Except.bind at j2; simp at j2
· unfold Except.bind; simp

end Except
