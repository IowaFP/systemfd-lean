
inductive Ctor1Variant : Type where
| refl
| sym
| fst
| snd
deriving Repr

inductive Ctor2Variant : Type where
| arrowk
| appk
| appt
| app
| cast
| seq
| appc
| apptc
| eq
deriving Repr

inductive Bind2Variant : Type where
| all
| lamt
| lam
| arrow
| allc
| arrowc
deriving Repr

inductive Term : Type where
| kind : Term -- □
| var : Nat -> Term
| type : Term -- ★
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| bind2 : Bind2Variant -> Term -> Term -> Term
| ite : Term   -- pattern
      -> Term  -- scrutinee
      -> Term  -- branch
      -> Term  -- continuation
      -> Term
| guard : Term  -- pattern
        -> Term -- scrutinee
        -> Term -- continuation
        -> Term
| letterm : Term -> Term -> Term -> Term

protected def Term.repr (a : Term) (p : Nat): Std.Format :=
  match a with
  | .kind => "□"
  | .var n => "#" ++ Nat.repr n
  | .type => "★"

  | .ctor1 .refl t => "≮" ++ Term.repr t p ++ "≯"
  | .ctor1 .sym t => "(sym! " ++ Term.repr t p ++ "!)"
  | .ctor1 .fst t => "(" ++ Term.repr t p ++ ")●1"
  | .ctor1 .snd t => "(" ++ Term.repr t p ++ ")●2"

  | .ctor2 .arrowk t1 t2 => Term.repr t1 p ++ Std.Format.line ++" → " ++ Term.repr t2 p
  | .ctor2 .appk t1 t2 => Std.Format.paren (Term.repr t1 p ++ " `@k " ++ Term.repr t2 p)
  | .ctor2 .appc t1 t2 => Std.Format.paren (Term.repr t1 p ++ " `@c " ++ Term.repr t2 p)
  | .ctor2 .appt t1 t2 => Std.Format.paren (Term.repr t1 p) ++ Std.Format.sbracket (Term.repr t2 p)
  | .ctor2 .apptc t1 t2 => Term.repr t1 p ++ " `@c[ " ++ Term.repr t2 p ++ " ]"
  | .ctor2 .app t1 t2 => Std.Format.paren (Term.repr t1 p ++ " ⬝ " ++ Std.Format.line ++ Term.repr t2 p)
  | .ctor2 .cast t1 t2 => Std.Format.paren (Term.repr t1 p  ++ " ▹ "  ++ Std.Format.line ++ Term.repr t2 p)
  | .ctor2 .seq t1 t2 => Term.repr t1 p ++ " `; "  ++ Std.Format.line ++ Term.repr t2 p
  | .ctor2 .eq t1 t2 => Term.repr t1 p ++ " ∼ " ++ Term.repr t2 p

  | .bind2 .all t1 t2 => "∀" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .arrow t1 t2 => Term.repr t1 p ++ " → " ++ Term.repr t2 p
  | .bind2 .arrowc t1 t2 => Term.repr t1 p ++ " → " ++ Term.repr t2 p
  | .bind2 .allc t1 t2 => "∀c" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .lamt t1 t2 => "Λ" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .lam t1 t2 => "`λ" ++ Std.Format.sbracket (Term.repr t1 p) ++ Std.Format.line ++ Term.repr t2 p

  | .ite pat s b c =>
         " match " ++ Term.repr s p ++ " with " ++
          Repr.addAppParen (Term.repr pat p) p ++ " ⇒ " ++ Term.repr b p ++ " | "
          ++ Term.repr c p ++ Std.Format.line
  | .guard pat s c =>
           Std.Format.nest 2 <| "If " ++ Term.repr pat p ++ " ← " ++ Term.repr s p ++ ", " ++ Std.Format.line
           ++ Term.repr c p
  | .letterm t t1 t2 => "let!" ++ Term.repr t1 p ++ " : " ++ Term.repr t p ++  " ;; " ++ Std.Format.line
                     ++ Term.repr t2 p


instance Term_repr : Repr Term where
  reprPrec a p := Term.repr a p

notation "★" => Term.type
infixr:14 " -k> " => Term.ctor2 Ctor2Variant.arrowk
infixr:14 " -t> " => Term.bind2 Bind2Variant.arrow
infixr:14 " -c> " => Term.bind2 Bind2Variant.arrowc
notation "∀[" A "]" B => Term.bind2 Bind2Variant.all A B
infixl:15 " `@k " => Term.ctor2 Ctor2Variant.appk
infixl:15 " `@t " => Term.ctor2 Ctor2Variant.appt
infixl:15 " `@ " => Term.ctor2 Ctor2Variant.app
notation "Λ[" A "]" t => Term.bind2 Bind2Variant.lamt A t
notation "`λ[" A "]" t => Term.bind2 Bind2Variant.lam A t
infixl:15 " ▹ " => Term.ctor2 Ctor2Variant.cast
prefix:max "#" => Term.var
notation "∀c[" A "]" B => Term.bind2 Bind2Variant.allc A B
infixl:15 " `; " => Term.ctor2 Ctor2Variant.seq
infixl:15 " `@c " => Term.ctor2 Ctor2Variant.appc
notation:15 f:15 " `@c[" a "]" => Term.ctor2 Ctor2Variant.apptc f a
infixl:15 " ~ " => Term.ctor2 Ctor2Variant.eq

prefix:max "refl! " => Term.ctor1 Ctor1Variant.refl
prefix:max "sym! " => Term.ctor1 Ctor1Variant.sym
postfix:max ".!1" => Term.ctor1 Ctor1Variant.fst
postfix:max ".!2" => Term.ctor1 Ctor1Variant.snd

namespace Term
  @[simp]
  def size : Term -> Nat
  | var _ => 0
  | kind => 0
  | type => 0
  | ctor1 _ t => (size t) + 1
  | ctor2 _ t1 t2 => (size t1) + (size t2) + 1
  | bind2 _ t1 t2 => (size t1) + (size t2) + 1
  | ite t1 t2 t3 t4 => (size t1) + (size t2) + (size t3) + (size t4) + 1
  | guard t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | letterm t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
end Term

instance sizeOf_Term : SizeOf Term where
  sizeOf := Term.size
