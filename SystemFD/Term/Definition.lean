
inductive Const : Type where
| pointed | unpointed
deriving Repr

inductive Term : Type where
| kind : Term
| var : Nat -> Term
| const : Const -> Term
| arrowk : Term -> Term -> Term
| all : Term -> Term -> Term
| arrow : Term -> Term -> Term
| appk : Term -> Term -> Term
| appt : Term -> Term -> Term
| app : Term -> Term -> Term
| lamt : Term -> Term -> Term
| lam : Term -> Term -> Term
| cast : Term -> Term -> Term
| ite : Term -> Term -> Term -> Term -> Term
| guard : Term -> Term -> Term -> Term
| refl : Term -> Term
| sym : Term -> Term
| seq : Term -> Term -> Term
| appc : Term -> Term -> Term
| fst : Term -> Term
| snd : Term -> Term
| allc : Term -> Term -> Term
| apptc : Term -> Term -> Term
| arrowc : Term -> Term -> Term
| eq : Term -> Term -> Term
| letopentype : Term -> Term -> Term
| letopen : Term -> Term -> Term
| letdata : Term -> Nat -> Term -> Term
| letctor : Term -> Term -> Term
| letterm : Term -> Term -> Term -> Term
| insttype : Term -> Term -> Term
| inst : Nat -> Term -> Term -> Term
deriving Repr

notation "★" => Term.const Const.pointed
notation "◯" => Term.const Const.unpointed
infixr:14 " -k> " => Term.arrowk
infixr:14 " -t> " => Term.arrow
infixr:14 " -c> " => Term.arrowc
notation:14 "∀[" A "]" B:14 => Term.all A B
infixl:15 " `@k " => Term.appk
infixl:15 " `@t " => Term.appt
infixl:15 " `@ " => Term.app
notation "Λ[" A "]" t:50 => Term.lamt A t
notation "`λ[" A "]" t:50 => Term.lam A t
infixl:15 " ▹ " => Term.cast
prefix:max "#" => Term.var
notation:14 "∀c[" A "]" B:14 => Term.allc A B
infixl:15 " `; " => Term.seq
infixl:15 " `@c " => Term.appc
notation:15 f:15 " `@c[" a "]" => Term.apptc f a
infixl:15 " ~ " => Term.eq

namespace Term
  @[simp]
  def size : Term -> Nat
  | var _ => 0
  | kind => 0
  | const _ => 0
  | arrowk t1 t2 => (size t1) + (size t2) + 1
  | all t1 t2 => (size t1) + (size t2) + 1
  | arrow t1 t2 => (size t1) + (size t2) + 1
  | arrowc t1 t2 => (size t1) + (size t2) + 1
  | appk t1 t2 => (size t1) + (size t2) + 1
  | appt t1 t2 => (size t1) + (size t2) + 1
  | app t1 t2 => (size t1) + (size t2) + 1
  | lamt t1 t2 => (size t1) + (size t2) + 1
  | lam t1 t2 => (size t1) + (size t2) + 1
  | cast t1 t2 => (size t1) + (size t2) + 1
  | ite t1 t2 t3 t4 => (size t1) + (size t2) + (size t3) + (size t4) + 1
  | guard t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | refl t => size t + 1
  | sym t => size t + 1
  | seq t1 t2 => (size t1) + (size t2) + 1
  | appc t1 t2 => (size t1) + (size t2) + 1
  | fst t => size t + 1
  | snd t => size t + 1
  | allc t1 t2 => (size t1) + (size t2) + 1
  | apptc t1 t2 => (size t1) + (size t2) + 1
  | eq t1 t2 => (size t1) + (size t2) + 1
  | letopentype t1 t2 => (size t1) + (size t2) + 1
  | letopen t1 t2 => (size t1) + (size t2) + 1
  | letdata t1 _ t2 => (size t1) + (size t2) + 1
  | letterm t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  | letctor t1 t2 => (size t1) + (size t2) + 1
  | insttype t1 t2 => (size t1) + (size t2) + 1
  | inst _ t1 t2 => (size t1) + (size t2) + 1
end Term
