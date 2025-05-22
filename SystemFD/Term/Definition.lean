
inductive Ctor1Variant : Type where
| sym
deriving Repr

inductive Ctor2Variant : Type where
| refl
| fst
| snd
| arrowk
| appk
| appt
| app
| cast
| seq
| appc
| apptc
| choice
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
| zero : Term
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| bind2 : Bind2Variant -> Term -> Term -> Term
| eq : Term -> Term -> Term -> Term
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
  | .zero => "0"

  | .ctor1 .sym t => "(sym! " ++ Term.repr t p ++ ")"
  | .ctor2 .fst t1 t2 => "(fst! " ++ Term.repr t1 p ++ ";" ++ Term.repr t2 p ++ ")"
  | .ctor2 .snd t1 t2 => "(snd! " ++ Term.repr t1 p ++ ";" ++ Term.repr t2 p ++ ")"

  | .ctor2 .refl t1 t2 => "(refl! " ++ Term.repr t1 p ++ "; " ++ Term.repr t2 p ++ ")"
  | .ctor2 .arrowk t1 t2 => Term.repr t1 p ++ Std.Format.line ++" → " ++ Term.repr t2 p
  | .ctor2 .appk t1 t2 => Std.Format.paren (Term.repr t1 p ++ " `@k " ++ Term.repr t2 p)
  | .ctor2 .appc t1 t2 => Std.Format.paren (Term.repr t1 p ++ " `@c " ++ Term.repr t2 p)
  | .ctor2 .appt t1 t2 => Std.Format.paren (Term.repr t1 p) ++ Std.Format.sbracket (Term.repr t2 p)
  | .ctor2 .apptc t1 t2 => Term.repr t1 p ++ " `@c[ " ++ Term.repr t2 p ++ " ]"
  | .ctor2 .app t1 t2 => Std.Format.paren (Term.repr t1 p ++ " ⬝ " ++ Std.Format.line ++ Term.repr t2 p)
  | .ctor2 .cast t1 t2 => Std.Format.paren (Term.repr t1 p  ++ " ▹ "  ++ Std.Format.line ++ Term.repr t2 p)
  | .ctor2 .seq t1 t2 => Term.repr t1 p ++ " `; "  ++ Std.Format.line ++ Term.repr t2 p
  | .ctor2 .choice t1 t2 => Term.repr t1 p ++ " ⊕ " ++ Term.repr t2 p

  | .bind2 .all t1 t2 => "∀" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .arrow t1 t2 => Term.repr t1 p ++ " → " ++ Term.repr t2 p
  | .bind2 .arrowc t1 t2 => Term.repr t1 p ++ " → " ++ Term.repr t2 p
  | .bind2 .allc t1 t2 => "∀c" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .lamt t1 t2 => "Λ" ++ Std.Format.sbracket (Term.repr t1 p) ++ Repr.addAppParen (Term.repr t2 p) p
  | .bind2 .lam t1 t2 => "`λ" ++ Std.Format.sbracket (Term.repr t1 p) ++ Std.Format.line ++ Term.repr t2 p

  | .eq t1 t2 t3 => Term.repr t1 p ++ " ∼[" ++ Term.repr t2 p ++ "]~ " ++ Term.repr t3 p
  | .ite pat s b c => Std.Format.paren (
         " match " ++ Term.repr s p ++ " with " ++
          Repr.addAppParen (Term.repr pat p) p ++ " ⇒ " ++ Term.repr b p ++ " | "
          ++ Term.repr c p ++ Std.Format.line)
  | .guard pat s c =>
           Std.Format.nest 2 <| "Guard " ++ Term.repr pat p ++ " ← " ++ Term.repr s p ++ ",  " ++ Std.Format.line
           ++ Term.repr c p
  | .letterm t t1 t2 => "let!" ++ Term.repr t1 p ++ " : " ++ Term.repr t p ++  " ;; " ++ Std.Format.line
                     ++ Term.repr t2 p


instance Term_repr : Repr Term where
  reprPrec a p := Term.repr a p

notation "★" => Term.type
notation "□" => Term.kind
notation:14 a " -k> " b => Term.ctor2 Ctor2Variant.arrowk a b
notation:14 a " -t> " b => Term.bind2 Bind2Variant.arrow a b
notation:14 a " -c> " b => Term.bind2 Bind2Variant.arrowc a b
notation "∀[" A "]" B => Term.bind2 Bind2Variant.all A B
notation:15 t1:15 " `@k " t2:16 => Term.ctor2 Ctor2Variant.appk t1 t2
notation:15 t1:15 " `@t " t2:16 => Term.ctor2 Ctor2Variant.appt t1 t2
notation:15 t1:15 " `@ " t2:16 => Term.ctor2 Ctor2Variant.app t1 t2
notation "Λ[" A "]" t => Term.bind2 Bind2Variant.lamt A t
notation "`λ[" A "]" t => Term.bind2 Bind2Variant.lam A t
notation:15 t1:16 " ▹ " t2:15 => Term.ctor2 Ctor2Variant.cast t1 t2
prefix:max "#" => Term.var
notation "∀c[" A "]" B => Term.bind2 Bind2Variant.allc A B
notation:15 t1:15 " `; " t2:16 => Term.ctor2 Ctor2Variant.seq t1 t2
notation:15 t1:15 " `@c " t2:16 => Term.ctor2 Ctor2Variant.appc t1 t2
notation:15 f:15 " `@c[" a "]" => Term.ctor2 Ctor2Variant.apptc f a
notation:15 A:15 " ~[" K "]~ " B:15 => Term.eq K A B
notation:15 "If " p " ← " s " then " i " else " e => Term.ite p s i e

prefix:max "refl! " => Term.ctor2 Ctor2Variant.refl
prefix:max "sym! " => Term.ctor1 Ctor1Variant.sym
prefix:max "fst!" => Term.ctor2 Ctor2Variant.fst
prefix:max "snd!" => Term.ctor2 Ctor2Variant.snd

notation "`0" => Term.zero
notation:20 t1:20 " ⊕ " t2:20 => Term.ctor2 Ctor2Variant.choice t1 t2

namespace Term
  @[simp]
  def size : Term -> Nat
  | var _ => 0
  | kind => 0
  | type => 0
  | zero => 0
  | ctor1 _ t => (size t) + 1
  | ctor2 _ t1 t2 => (size t1) + (size t2) + 1
  | bind2 _ t1 t2 => (size t1) + (size t2) + 1
  | eq t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | ite t1 t2 t3 t4 => (size t1) + (size t2) + (size t3) + (size t4) + 1
  | guard t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | letterm t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
end Term

instance sizeOf_Term : SizeOf Term where
  sizeOf := Term.size
