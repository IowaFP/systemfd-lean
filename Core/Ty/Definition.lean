import Core.Vec
import Lilac
open Lilac


namespace Core
-- inductive BaseKind : Type where
-- | closed
-- | «open»

-- notation "b★" => BaseKind.closed
-- notation "b◯" => BaseKind.open

inductive Kind : Type where
| base : Kind
| arrow : Kind -> Kind -> Kind

notation "★" => Kind.base
-- notation "◯" => Kind.base BaseKind.open
infixr:64 " -:> " => Kind.arrow

inductive Ty : Type where
| var : Nat -> Ty
| global : String -> Ty
| arrow : Ty -> Ty -> Ty
| all : Kind -> Ty -> Ty
| app : Ty -> Ty -> Ty
| eq : Kind -> Ty -> Ty -> Ty

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
| app t1 t2 => t1.size + t2.size + 1
| eq _ t1 t2 => t1.size + t2.size + 1

instance instSizeOf_Ty : SizeOf Ty where
  sizeOf := Ty.size

prefix:max "t#" => Ty.var
prefix:max "gt#" => Ty.global
infixr:64 " -:> " => Ty.arrow
notation "∀[" K "]" B => Ty.all K B
infixl:54 " • " => Ty.app
notation:55 A:55 " ~[" K "]~ " B => Ty.eq K A B

protected def Kind.repr (p : Nat) : (a : Kind) -> Std.Format
| base => "★"
-- | base .open => "◯"
| arrow k1 k2 => Repr.addAppParen ((Kind.repr max_prec k1) ++ " -:> " ++ Kind.repr p k2) p

instance kindRepr : Repr Kind where
  reprPrec a p := Kind.repr p a

protected def Ty.repr (p : Nat) : (a : Ty) -> Std.Format
| var n => "t#" ++ Nat.repr n
| global s => "gt#" ++ s
| arrow t1 t2 => Repr.addAppParen (Ty.repr max_prec t1 ++ " -:> " ++ Ty.repr p t2) p
| all K t => Repr.addAppParen ("∀[ " ++ repr K ++ " ] " ++ Ty.repr max_prec t) p
| eq K A B => Repr.addAppParen (Ty.repr max_prec A ++ " ~[" ++ repr K ++ "]~ " ++ Ty.repr max_prec B) p
| app t1 t2 => Repr.addAppParen (Ty.repr p t1 ++ " • " ++ Ty.repr max_prec t2) p

instance instRepr_Ty : Repr Ty where
  reprPrec a p := Ty.repr p a

def Vec.Ty.repr (vs : Lilac.Vec Ty n) : Std.Format := "#(" ++ vs.reprPrec 0 ++ ")"

def Vec.Kind.repr (vs : Vec Kind n) : Std.Format := "#(" ++ vs.reprPrec 0 ++ ")"

def SpineTy.repr : SpineTy -> Std.Format
| ⟨_, vm, _, vn, _, vu, R⟩ =>
  "⟨" /-++ Nat.repr m ++ ", " -/ ++ Vec.Kind.repr vm ++ ", "
      /-++ Nat.repr n ++ ", " -/ ++ Vec.Kind.repr vn ++ ", "
      /-++ Nat.repr u ++ ", " -/ ++ Vec.Ty.repr vu ++ ", "
      ++ R.repr 0 ++"⟩"


end Core
/-

case var => _
case global => _
case arrow => _
case eq => _
case app => _
case all => _

-/
