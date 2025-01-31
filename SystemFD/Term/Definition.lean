
inductive Const : Type where
| pointed | unpointed
deriving Repr

inductive Ctor1Variant : Type where
| refl
| sym
| fst
| snd
deriving Repr

inductive Ctor2Variant : Type where
| arrowk
| arrow
| appk
| appt
| app
| cast
| seq
| appc
| apptc
| arrowc
| eq
deriving Repr

inductive Bind2Variant : Type where
| all
| lamt
| lam
| allc
| letopentype
| letopen
| letctor
| insttype
deriving Repr

inductive Term : Type where
| kind : Term
| var : Nat -> Term
| const : Const -> Term
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| bind2 : Bind2Variant -> Term -> Term -> Term
| ite : Term -> Term -> Term -> Term -> Term
| guard : Term -> Term -> Term -> Term
| letdata : Term -> Nat -> Term -> Term
| letterm : Term -> Term -> Term -> Term
| inst : Nat -> Term -> Term -> Term
deriving Repr

notation "★" => Term.const Const.pointed
notation "◯" => Term.const Const.unpointed
infixr:14 " -k> " => Term.ctor2 Ctor2Variant.arrowk
infixr:14 " -t> " => Term.ctor2 Ctor2Variant.arrow
infixr:14 " -c> " => Term.ctor2 Ctor2Variant.arrowc
notation:14 "∀[" A "]" B:14 => Term.bind2 Bind2Variant.all A B
infixl:15 " `@k " => Term.ctor2 Ctor2Variant.appk
infixl:15 " `@t " => Term.ctor2 Ctor2Variant.appt
infixl:15 " `@ " => Term.ctor2 Ctor2Variant.app
notation "Λ[" A "]" t:50 => Term.bind2 Bind2Variant.lamt A t
notation "`λ[" A "]" t:50 => Term.bind2 Bind2Variant.lam A t
infixl:15 " ▹ " => Term.ctor2 Ctor2Variant.cast
prefix:max "#" => Term.var
notation:14 "∀c[" A "]" B:14 => Term.bind2 Bind2Variant.allc A B
infixl:15 " `; " => Term.ctor2 Ctor2Variant.seq
infixl:15 " `@c " => Term.ctor2 Ctor2Variant.appc
notation:15 f:15 " `@c[" a "]" => Term.ctor2 Ctor2Variant.apptc f a
infixl:15 " ~ " => Term.ctor2 Ctor2Variant.eq

prefix:max "refl! " => Term.ctor1 Ctor1Variant.refl
prefix:max "sym! " => Term.ctor1 Ctor1Variant.sym
postfix:max ".!1" => Term.ctor1 Ctor1Variant.fst
postfix:max ".!2" => Term.ctor1 Ctor1Variant.snd

prefix:max "letopentype!" => Term.bind2 Bind2Variant.letopentype
prefix:max "letopen!" => Term.bind2 Bind2Variant.letopen
prefix:max "letctor!" => Term.bind2 Bind2Variant.letctor
prefix:max "insttype!" => Term.bind2 Bind2Variant.insttype

namespace Term
  @[simp]
  def size : Term -> Nat
  | var _ => 0
  | kind => 0
  | const _ => 0
  | ctor1 _ t => (size t) + 1
  | ctor2 _ t1 t2 => (size t1) + (size t2) + 1
  | bind2 _ t1 t2 => (size t1) + (size t2) + 1
  | ite t1 t2 t3 t4 => (size t1) + (size t2) + (size t3) + (size t4) + 1
  | guard t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | letdata t1 _ t2 => (size t1) + (size t2) + 1
  | letterm t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | inst _ t1 t2 => (size t1) + (size t2) + 1
end Term
