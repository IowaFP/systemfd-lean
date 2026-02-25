import LeanSubst
import Surface.Ty
import Core.Vec

open LeanSubst

namespace Surface

inductive Term : Type where
| var : Nat -> Term
| global : String -> Term
| appt : Term -> Ty -> Term
| app : Term -> Term -> Term
| lamt :  Kind -> Term -> Term
| lam : Ty -> Term -> Term
| «match» : Term -> Vect n Term -> Vect n Term -> Term -> Term
-- |  hole : Ty  -> Term


prefix:max "`#" => Term.var
prefix:max "g`#" => Term.global

notation f " `•[" a "]" => Term.appt f a

notation:70 f " `• " a:70 => Term.app f a
-- notation f " ∘[" a "]" => Term.ctor2 (Ctor2Variant.app BaseKind.open) f a

-- bind notation
notation "Λˢ[" K "]" t => Term.lamt K t
notation "λˢ[" A "]" t => Term.lam A t

notation "matchˢ!" => Term.match


protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "`#" ++ Nat.repr n
| .global n => "g`#" ++ n
| .app t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " • " ++Term.repr p t2) p
| .appt t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " •" ++ Std.Format.sbracket (Ty.repr p t2)) p
| .lamt K t =>
  Repr.addAppParen ("Λˢ" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .lam τ t => Repr.addAppParen ("λˢ" ++ Std.Format.sbracket (repr τ) ++ " " ++ Term.repr max_prec t) p
| .match (n := n) s pats ts allc =>
  let ts : Vect n Std.Format := λ i =>
    let t := ts i
    let pat := pats i
    Std.Format.nest 4 <| Std.Format.line ++ Term.repr p pat ++ " => " ++ Term.repr p t
  let css := Vect.fold Std.Format.nil (·++·) ts
  Std.Format.nest 4 <| (("match " ++ Term.repr max_prec s ++ " with")
    ++ css
    ++ (Std.Format.nest 4 <| Std.Format.line ++ " _ => " ++ Term.repr p allc)
    )

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a

@[simp]
def Term.size : Term -> Nat
| var _ => 0
| global _ => 0
| app t1 t2 => t1.size + t2.size + 1
| appt t1 _ => size t1 + 1
| lamt _ t => size t + 1
| lam _ t => size t + 1
| «match» t1 t2 t3 t4 =>
  let t2' : Vect _ _ := size <$> t2
  let t3' : Vect _ _ := size <$> t3
  size t1 + List.sum t2' + List.sum t3' + size t4 + 1


end Surface
