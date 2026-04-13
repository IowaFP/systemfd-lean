import LeanSubst
import Lilac.Vect

import Core.Ty
import Core.Vec

open LeanSubst
open Vect

namespace Core
inductive Ctor0Variant : Type where
| zero
| refl (A : Ty)

inductive Ctor1Variant : Type where
| sym
| prj (n : Nat)
| appt (a : Ty)

inductive Ctor2Variant : Type where
| app (b : BaseKind)
| cast
| seq
| appc
| apptc
| arrowc
| choice

inductive TyBindVariant : Type where
| lamt
| allc

abbrev Pattern m := Vect m (String × List Ty × Nat)

def Pattern.bind : Pattern m -> Nat := Vect.fold 0 (λ (_, _, n) acc => n + acc)

inductive Term : Type where
| var : Nat -> Term
| global : String -> Term
| dctor n : String -> List Ty -> Vect n Term -> Term
| ctor0 : Ctor0Variant -> Term
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| tbind : TyBindVariant -> Kind -> Term -> Term
| lam : Ty -> Term -> Term
| guard : Term -> Term -> Term -> Term
| cast : Ty -> Term -> Term -> Term
| mtch m n : Vect m Term -> Vect n (Pattern m) -> Vect n Term -> Term

def Constructor := String × List Ty × List Term

prefix:max "#" => Term.var
prefix:max "g#" => Term.global

-- ctor0 notation
notation "`0" => Term.ctor0 Ctor0Variant.zero
notation "refl! " A => Term.ctor0 (Ctor0Variant.refl A)

-- ctor1 notation
prefix:max "sym!" => Term.ctor1 Ctor1Variant.sym
notation "prj[" n "]" t => Term.ctor1 (Ctor1Variant.prj n) t
notation "snd!" t => Term.ctor1 Ctor1Variant.snd t
notation f " •[" a "]" => Term.ctor1 (Ctor1Variant.appt a) f

-- ctor2 notation
notation:70 f " •(" b ") " a:70 => Term.ctor2 (Ctor2Variant.app b) f a
notation:70 f " • " a:70 => Term.ctor2 (Ctor2Variant.app BaseKind.closed) f a
notation f " ∘[" a "]" => Term.ctor2 (Ctor2Variant.app BaseKind.open) f a
notation t " ▹ " c => Term.ctor2 Ctor2Variant.cast t c
notation t1 " `; " t2 => Term.ctor2 Ctor2Variant.seq t1 t2
notation f " •c " a => Term.ctor2 Ctor2Variant.appc f a
notation f " •c[" a "]" => Term.ctor2 Ctor2Variant.apptc f a
notation A " -c> " B => Term.ctor2 Ctor2Variant.arrowc A B
notation t1 " `+ " t2 => Term.ctor2 Ctor2Variant.choice t1 t2

-- bind notation
notation "Λ[" K "]" t => Term.tbind TyBindVariant.lamt K t
notation "λ[" A "]" t => Term.lam A t
notation "∀c[" K "]" P => Term.tbind TyBindVariant.allc K P

@[simp]
def Term.size : Term -> Nat
| var _ => 0
| global _ => 0
| dctor _ _ _ t2 =>
  let t2' : Vect _ _ := size <$> t2
  List.sum t2' + 1
| ctor0 _ => 0
| ctor1 _ t => size t + 1
| ctor2 _ t1 t2 => size t1 + size t2 + 1
| tbind _ _ t => size t + 1
| lam _ t => size t + 1
| guard t1 t2 t3 => size t1 + size t2 + size t3 + 1
| cast _ t1 t2 => size t1 + size t2 + 1
| mtch _ _ t1 _ t3 =>
  let t1' : Vect _ _ := size <$> t1
  let t3' : Vect _ _ := size <$> t3
  List.sum t1' + List.sum t3' + 1

@[simp]
instance instSizeOf_Term : SizeOf Term where
  sizeOf := Term.size

protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "#" ++ Nat.repr n
| .global n => "g#" ++ n
| dctor _ _ _ _ => "don't care"
| .ctor0 (.refl t) => Std.Format.paren ("refl! " ++ Ty.repr max_prec t)
| .ctor0 .zero => "`0"
| .ctor1 .sym t => "(sym! " ++ Term.repr p t ++ ")"
| .ctor1 (.prj n) t => "(prj! " ++ Nat.repr n ++ " " ++ Term.repr p t ++ ")"
| .ctor1 (.appt τ) t => Repr.addAppParen (Term.repr max_prec t ++ " •[" ++ repr τ ++ "]") p
| .ctor2 (.app .closed) t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " • " ++Term.repr p t2) p
| .ctor2 (.app .open) t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " ∘" ++ Std.Format.sbracket (Term.repr p t2)) p
| .ctor2 .cast t1 t2 =>
  Repr.addAppParen ((Term.repr max_prec t1 ++ " • " ++ Term.repr p t2)) p
| .ctor2 .seq t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ "`;" ++
  Std.Format.line ++ Term.repr p t2) p
| .ctor2 .appc t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " •c " ++
  Std.Format.line ++ Term.repr max_prec t2) p
| .ctor2 .apptc t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++
  Std.Format.line ++ " •c" ++ Std.Format.sbracket (Term.repr p t2)) p
| .ctor2 .arrowc t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " -c> " ++ Term.repr p t2) p
| .ctor2 .choice t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " `+ " ++ Term.repr max_prec t2) p
| .tbind .lamt K t =>
  Repr.addAppParen ("Λ" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .tbind .allc K t =>
  Repr.addAppParen ("∀c" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .lam τ t => Repr.addAppParen ("λ" ++ Std.Format.sbracket (repr τ) ++ " " ++ Term.repr max_prec t) p
| .cast _ _ _ => "don't care"
| .mtch _ _ _ _ _ => "don't care"
  -- let ts : Vect n Std.Format := λ i =>
  --   let t := ts i
  --   let pat := pats i
  --   Std.Format.nest 4 <| Std.Format.line ++ Term.repr p pat ++ " => " ++ Term.repr p t
  -- let css := Vect.fold Std.Format.nil (·++·) ts
  -- Std.Format.nest 4 <| (("match " ++ Term.repr max_prec s ++ " with")
  --   ++ css
  --   ++ (Std.Format.nest 4 <| Std.Format.line ++ " _ => " ++ Term.repr p allc)
  --   )
| .guard pat s t =>
  Std.Format.nest 4 <| ("guard " ++ Term.repr p pat ++ " ← " ++ Term.repr p s) ++
  Std.Format.line ++ Term.repr p t

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a
end Core
