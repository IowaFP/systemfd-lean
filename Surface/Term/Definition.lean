import LeanSubst
-- import Surface.Ty
import Core.Ty
import Common.Vec
import Core.Term

open LeanSubst
open Lilac

namespace Surface

inductive Term : Type where
| var : Nat -> Term
| global : {n m p : Nat} -> String -> Vec Core.Ty n -> Vec Core.Ty m -> Fun.Vec Term p -> Term
| appt : Term -> Core.Ty -> Term
| app : Term -> Term -> Core.Ty -> Term
| lamt :  Core.Kind -> Term -> Term
| lam : Core.Ty -> Term -> Term
| mtch m n : Fun.Vec Term m -> Fun.Vec Core.Ty m -> Fun.Vec (Core.Pattern m) n -> Fun.Vec Term n -> Core.Ty -> Term
| annot : Term -> Core.Ty -> Term


def mtch' (τ : Core.Ty) (sts : Vec (Term × Core.Ty) m) (pat_cube : Vec (Core.Pattern m × Term) n) : Term :=
  let ss := Vec.map (·.1) sts
  let τs := Vec.map (·.2) sts
  let p := Vec.map (·.1) pat_cube
  let x := Vec.map (·.2) pat_cube
  .mtch m n ss.to τs.to p.to x.to τ


prefix:max "`#" => Term.var
notation:70 "g`#" x "`•ᵤ" a "`•ₑ" b "`•ₜ" c => Term.global x a b c

notation f " `•[" a "]" => Term.appt f a

notation:70 f " `• " a:70 " :: " τ:70 => Term.app f a τ
-- notation f " ∘[" a "]" => Term.ctor2 (Ctor2Variant.app BaseKind.open) f a

-- bind notation
notation "Λˢ[" K "]" t => Term.lamt K t
notation "λˢ[" A "]" t => Term.lam A t

-- notation "matchˢ!" => Term.match


protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "`#" ++ Nat.repr n
| .global (p := p) n τU τE as =>
  let as : Fun.Vec Std.Format p := λ i => Term.repr p (as i)
  "g`#" ++ n ++ " `•ᵤ " ++ (τU.repr max_prec) ++ " `•ₑ " ++ (τE.repr max_prec) ++ " `• " ++ as.to.foldl (·++·) Std.Format.nil
| .app t1 t2 τ =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " • " ++ (Term.repr p t2 ++ " : " ++ τ.repr max_prec)) p
| .appt t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " •" ++ Std.Format.sbracket (t2.repr p)) p
| .lamt K t =>
  Repr.addAppParen ("Λˢ" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .lam τ t => Repr.addAppParen ("λˢ" ++ Std.Format.sbracket (repr τ) ++ " " ++ Term.repr max_prec t) p
| .mtch m n ss ssτ pats bs ty =>
  let ss' : Fun.Vec Std.Format m := λ i =>
    Term.repr max_prec (ss i)  ++ " :: " ++ Core.Ty.repr max_prec (ssτ i)
  let ss' := ss'.to.foldl (init := Std.Format.nil) (· ++ ·)
  let ts : Fun.Vec Std.Format n := λ i =>
    let t := bs i
    let pat := pats i
    Std.Format.nest 4 <| Std.Format.line ++ " | "++ pat.repr ++ " -> " ++ Term.repr p t
  let bs := ts.to.foldl (·++·) Std.Format.nil
  Std.Format.nest 4 <| ("match " ++ ss' ++ "with" ++ Std.Format.line ++ bs)
| annot t ty =>
  Std.Format.paren (Term.repr p t ++ " : " ++ repr ty)

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a

@[simp]
def Term.size : Term -> Nat
| var _ => 1
| global _ _ _ as => (Fun.Vec.to (Term.size <$> as)).sum + 1
| app t1 t2 _ => t1.size + t2.size + 1
| appt t1 _ => size t1 + 1
| lamt _ t => size t + 1
| lam _ t => size t + 1
| mtch _ _ t1 _ _ t2 _ =>
   (Fun.Vec.to (Term.size <$> t1)).sum + (Fun.Vec.to (Term.size <$> t2)).sum + 1
| annot t _ => size t + 1

end Surface
