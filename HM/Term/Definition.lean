import Core.Ty
import Common.Vec

open LeanSubst
open Lilac

namespace HM

inductive Term : Type where
| var  : Nat -> Term
| defn : String -> Term
| lam  : Term -> Term
| app  : Term -> Term -> Term

prefix:max "#" => Term.var
prefix:max "d#" => Term.var

notation:70 f " • " a:70 => Term.app f a

-- bind notation
notation "`λ" t => Term.lam t


@[simp]
def Term.size : Term -> Nat
| var _ => 0
| defn _ => 0
| lam t => size t + 1
| app t1 t2 => size t1 + size t2 + 1

@[simp]
instance instSizeOf_Term : SizeOf Term where
  sizeOf := Term.size

protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "#" ++ Nat.repr n
| .defn n => "d#" ++ n
| .lam t => Repr.addAppParen ("λ" ++ Term.repr max_prec t) p
| .app t1 t2 => Repr.addAppParen (Term.repr max_prec t1 ++ "•" ++ Term.repr max_prec t2) max_prec

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a
end HM
