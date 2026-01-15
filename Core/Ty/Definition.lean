inductive BaseKind : Type where
| «open» | closed

inductive Kind : Type where
| base : BaseKind -> Kind
| arrow : Kind -> Kind -> Kind

notation "★" => Kind.base BaseKind.closed
notation "◯" => Kind.base BaseKind.open
infixr:64 " -:> " => Kind.arrow

inductive Ty : Type where
| var : Nat -> Ty
| global : String -> Ty
| arrow : Ty -> Ty -> Ty
| all : Kind -> Ty -> Ty
| app : Ty -> Ty -> Ty
| eq : Kind -> Ty -> Ty -> Ty

prefix:max "t#" => Ty.var
prefix:max "gt#" => Ty.global
infixr:64 " -:> " => Ty.arrow
notation "∀[" K "]" B => Ty.all K B
infixl:54 " • " => Ty.app
notation:55 A:55 " ~[" K "]~ " B => Ty.eq K A B
