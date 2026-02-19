import LeanSubst
import Surface.Ty
import Core.Vec

open LeanSubst

inductive Surface.Term : Type where
| var : Nat -> Term
| global : String -> Term
| appt : Term -> Surface.Ty -> Term
| app : Term -> Term -> Term
| lamt :  Surface.Kind -> Term -> Term
| lam : Surface.Ty -> Term -> Term
| «match» : Term -> Vec Term n -> Vec Term n -> Term -> Term
-- |  hole : Ty  -> Term


prefix:max "`#" => Surface.Term.var
prefix:max "g`#" => Surface.Term.global

notation f " `•[" a "]" => Surface.Term.appt f a

notation:70 f " `• " a:70 => Surface.Term.app f a
-- notation f " ∘[" a "]" => Surface.Term.ctor2 (Ctor2Variant.app BaseKind.open) f a

-- bind notation
notation "Λˢ[" K "]" t => Surface.Term.lamt K t
notation "λˢ[" A "]" t => Surface.Term.lam A t

notation "matchˢ!" => Surface.Term.match


protected def Surface.Term.repr (p : Nat) : (a : Term) -> Std.Format
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
  let ts : Vec Std.Format n := λ i =>
    let t := ts i
    let pat := pats i
    Std.Format.nest 4 <| Std.Format.line ++ Term.repr p pat ++ " => " ++ Term.repr p t
  let css := Vec.fold (·++·) Std.Format.nil ts
  Std.Format.nest 4 <| (("match " ++ Term.repr max_prec s ++ " with")
    ++ css
    ++ (Std.Format.nest 4 <| Std.Format.line ++ " _ => " ++ Term.repr p allc)
    )

@[simp]
instance Surface.instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a
