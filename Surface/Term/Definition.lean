import LeanSubst
-- import Surface.Ty
import Core.Ty
import Core.Vec

open LeanSubst
open Lilac

namespace Surface

inductive Term : Type where
| var : Nat -> Term
| global : String -> Term
| appt : Term -> Core.Ty -> Term
| app : Term -> Term -> Term
| lamt :  Core.Kind -> Term -> Term
| lam : Core.Ty -> Term -> Term
-- | «match» : (n : Nat) -> Ty -> Term -> Fun.Vec Term n -> Fun.Vec Term n -> Term -> Term
| annot : Term -> Core.Ty -> Term


prefix:max "`#" => Term.var
prefix:max "g`#" => Term.global

notation f " `•[" a "]" => Term.appt f a

notation:70 f " `• " a:70 => Term.app f a
-- notation f " ∘[" a "]" => Term.ctor2 (Ctor2Variant.app BaseKind.open) f a

-- bind notation
notation "Λˢ[" K "]" t => Term.lamt K t
notation "λˢ[" A "]" t => Term.lam A t

-- notation "matchˢ!" => Term.match


protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "`#" ++ Nat.repr n
| .global n => "g`#" ++ n
| .app t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " • " ++ Term.repr p t2) p
| .appt t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " •" ++ Std.Format.sbracket (t2.repr p)) p
| .lamt K t =>
  Repr.addAppParen ("Λˢ" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .lam τ t => Repr.addAppParen ("λˢ" ++ Std.Format.sbracket (repr τ) ++ " " ++ Term.repr max_prec t) p
-- | .match n _ s pats ts d =>
--   let ts : Fun.Vec Std.Format n := λ i =>
--     let t := ts i
--     let pat := pats i
--     Std.Format.nest 4 <| Std.Format.line ++ Term.repr p pat ++ " -> " ++ Term.repr p t
--   let css := ts.to.foldl (·++·) Std.Format.nil
--   Std.Format.nest 4 <| (("match " ++ Term.repr max_prec s ++ " with")
--     ++ css
--     ++ (Std.Format.nest 4 <| Std.Format.line ++ " _ -> " ++ Term.repr p d)
--     )
| annot t ty =>
  Std.Format.paren (Term.repr p t ++ " : " ++ repr ty)

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a

@[simp]
def Term.size : Term -> Nat
| var _ => 1
| global _ => 1
| app t1 t2 => t1.size + t2.size + 1
| appt t1 _ => size t1 + 1
| lamt _ t => size t + 1
| lam _ t => size t + 1
-- | «match» _ _ t1 t2 t3 t4 =>
--  size t1 + t2.to.length + t3.to.length + size t4 + 1
| annot t _ => size t + 1

end Surface
