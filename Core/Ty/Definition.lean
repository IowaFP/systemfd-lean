
inductive BaseKind : Type where
| closed
| «open»

inductive Kind : Type where
| base : BaseKind -> Kind
| arrow : Kind -> Kind -> Kind

notation "★" => Kind.base BaseKind.closed
notation "◯" => Kind.base BaseKind.open
infixr:64 " -:> " => Kind.arrow

inductive Ty : Type where
| var : Nat -> Ty
| global : String -> Ty
| arrow : BaseKind -> Ty -> Ty -> Ty
| all : Kind -> Ty -> Ty
| app : Ty -> Ty -> Ty
| eq : Kind -> Ty -> Ty -> Ty

prefix:max "t#" => Ty.var
prefix:max "gt#" => Ty.global
notation A:64 " -[" b "]>" B:65 => Ty.arrow b A B
infixr:64 " -:> " => Ty.arrow BaseKind.closed
infixr:64 " =:> " => Ty.arrow BaseKind.open
notation "∀[" K "]" B => Ty.all K B
infixl:54 " • " => Ty.app
notation:55 A:55 " ~[" K "]~ " B => Ty.eq K A B

protected def Kind.repr (p : Nat) : (a : Kind) -> Std.Format
| base .closed => "★"
| base .open => "◯"
| arrow k1 k2 => Repr.addAppParen ((Kind.repr max_prec k1) ++ " -:> " ++ Kind.repr p k2) p

instance kindRepr : Repr Kind where
  reprPrec a p := Kind.repr p a

protected def Ty.repr (p : Nat) : (a : Ty) -> Std.Format
| var n => "t#" ++ Nat.repr n
| global s => "gt#" ++ s
| arrow .closed t1 t2 => Repr.addAppParen (Ty.repr max_prec t1 ++ " -:> " ++ Ty.repr p t2) p
| arrow .open t1 t2 => Repr.addAppParen (Ty.repr max_prec t1 ++ " =:> " ++ Ty.repr p t2) p
| all K t => Repr.addAppParen ("∀[ " ++ repr K ++ " ] " ++ Ty.repr max_prec t) p
| eq K A B => Repr.addAppParen (Ty.repr max_prec A ++ " ~[" ++ repr K ++ "]~ " ++ Ty.repr max_prec B) p
| app t1 t2 => Repr.addAppParen (Ty.repr p t1 ++ " • " ++ Ty.repr max_prec t2) p

instance tyRepr : Repr Ty where
  reprPrec a p := Ty.repr p a
