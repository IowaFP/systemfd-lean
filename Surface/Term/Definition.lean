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


prefix:max "`#" => Surface.Term.var
prefix:max "g`#" => Surface.Term.global

notation f " `•[" a "]" => Surface.Term.appt f a

notation:70 f " • " a:70 => Surface.Term.app f a
-- notation f " ∘[" a "]" => Surface.Term.ctor2 (Ctor2Variant.app BaseKind.open) f a

-- bind notation
notation "Λˢ[" K "]" t => Surface.Term.lamt K t
notation "`λˢ[" A "]" t => Surface.Term.lam A t

notation "matchˢ!" => Surface.Term.match
