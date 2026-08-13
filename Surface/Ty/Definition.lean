import Core.Vec
import Lilac
open Lilac

namespace Surface

inductive BaseKind : Type where
| closed
| «open»

notation "b`★" => Surface.BaseKind.closed
notation "b`◯" => Surface.BaseKind.open

inductive Kind : Type where
| base : BaseKind -> Kind
| arrow : Kind -> Kind -> Kind

notation "`★" => Surface.Kind.base Surface.BaseKind.closed
notation "`◯" => Surface.Kind.base Surface.BaseKind.open
infixr:64 " `-:> " => Surface.Kind.arrow

def Kind.mk_kind : Vec Kind n -> Kind := Vec.foldl (init := `★) (λ acc n => n `-:> acc)

inductive Ty : Type where
| var : Nat -> Ty
| global : String -> Ty
| arrow : Ty -> Ty -> Ty
| «then» : Ty -> Ty -> Ty
| all : Kind -> Ty -> Ty
| app : Ty -> Ty -> Ty

-- Us -> Es -> Ts -> R
-- Us = "Universally quantified" types, will be applied in a pattern
-- Es = "Existentionally quantified" types, will be bound by a pattern
-- Ts = Subdata, will be bound by a pattern
-- R = Return type (datatype for constructors, anything for an open method)
abbrev SpineTy := (m1 : Nat) × Vec Kind m1 × (m2 : Nat) × Vec Kind m2 × (n : Nat) × Vec Ty n × Ty


def Ty.size : Ty -> Nat
| var _ => 0
| global _ => 0
| all _ t => t.size + 1
| arrow t1 t2 => t1.size + t2.size + 1
| «then» t1 t2 => t1.size + t2.size + 1
| app t1 t2 => t1.size + t2.size + 1

instance instSizeOf_Ty : SizeOf Surface.Ty where
  sizeOf := Surface.Ty.size

prefix:max "t`#" => Surface.Ty.var
prefix:max "gt`#" => Surface.Ty.global
infixr:64 " `-:> " => Surface.Ty.arrow
infixr:64 " `=:> " => Surface.Ty.then
notation "`∀[" K "]" B => Surface.Ty.all K B
-- infixl:54 " `• " => Surface.Ty.app

protected def Kind.repr (p : Nat) : (a : Kind) -> Std.Format
| base .closed => "`★"
| base .open => "`◯"
| arrow k1 k2 => Repr.addAppParen ((Kind.repr max_prec k1) ++ " `-:> " ++ Kind.repr p k2) p

instance Surface.kindRepr : Repr Surface.Kind where
  reprPrec a p := Surface.Kind.repr p a

protected def Ty.repr (p : Nat) : (a : Ty) -> Std.Format
| var n => "t`#" ++ Nat.repr n
| global s => "gt`#" ++ s
| arrow t1 t2 => Repr.addAppParen (Ty.repr max_prec t1 ++ " `-:> " ++ Ty.repr p t2) p
| «then» t1 t2 => Repr.addAppParen (Ty.repr max_prec t1 ++ " `=:> " ++ Ty.repr p t2) p
| all K t => Repr.addAppParen ("`∀[ " ++ repr K ++ " ] " ++ Ty.repr max_prec t) p
| app t1 t2 => Repr.addAppParen (Ty.repr p t1 ++ " `• " ++ Ty.repr max_prec t2) p

instance tyRepr : Repr Ty where
  reprPrec a p := Ty.repr p a


/-

case var => sorry
case global => sorry
case arrow => sorry
case app => sorry
case all => sorry

-/

end Surface
