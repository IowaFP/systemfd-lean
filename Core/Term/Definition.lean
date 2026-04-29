
import Core.Ty
import Core.Vec

open LeanSubst
open Lilac

namespace Core

inductive Ctor0Variant : Type where
| fail
| refl (A : Ty)

inductive SpCtorVariant : Type where
| openm
| odata
| cdata

inductive Ctor1Variant : Type where
| prj (n : Nat)
| appt (a : Ty)

inductive Ctor2Variant : Type where
| app
| apptc

inductive TyBindVariant : Type where
| lamt
| allc

abbrev Pattern m := Vec (String × List Ty × Nat) m

def Pattern.bind : Pattern m -> Nat
| .nil => 0
| .cons (_, _, n) tl => n + Pattern.bind tl

inductive Term : Type where
| var : Nat -> Term
| defn : String -> Term
| spctor : SpCtorVariant -> String -> List Ty -> Fun.Vec Term n -> Term
| ctor0 : Ctor0Variant -> Term
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| tbind : TyBindVariant -> Kind -> Term -> Term
| lam : Ty -> Term -> Term
| cast : Ty -> Term -> Term -> Term
| mtch m n : Fun.Vec Term m -> Fun.Vec (Pattern m) n -> Fun.Vec Term n -> Term

def Constructor := String × List Ty × List Term

prefix:max "#" => Term.var
prefix:max "d#" => Term.defn

-- spctor notation
notation "ctor!" => Term.spctor SpCtorVariant.cdata
notation "inst!" => Term.spctor SpCtorVariant.odata
notation "openm!" => Term.spctor SpCtorVariant.openm

-- ctor0 notation
notation "fail!" => Term.ctor0 Ctor0Variant.fail
notation "refl! " A => Term.ctor0 (Ctor0Variant.refl A)

-- ctor1 notation
notation "prj[" n "]" t => Term.ctor1 (Ctor1Variant.prj n) t
notation f " •[" a "]" => Term.ctor1 (Ctor1Variant.appt a) f

-- ctor2 notation
notation:70 f " •(" b ") " a:70 => Term.ctor2 (Ctor2Variant.app b) f a
notation:70 f " • " a:70 => Term.ctor2 Ctor2Variant.app f a
-- notation f " ∘[" a "]" => Term.ctor2 (Ctor2Variant.app BaseKind.open) f a
notation t " ▹ " c => Term.ctor2 Ctor2Variant.cast t c
notation f " •c[" a "]" => Term.ctor2 Ctor2Variant.apptc f a

-- bind notation
notation "Λ[" K "]" t => Term.tbind TyBindVariant.lamt K t
notation "λ[" A "]" t => Term.lam A t
notation "∀c[" K "]" P => Term.tbind TyBindVariant.allc K P

def mtch' (sts : Vec Term m) (pat_cube : Vec (Pattern m × Term) n) : Term :=
  let p := Vec.map (·.1) pat_cube
  let x := Vec.map (·.2) pat_cube
  .mtch m n sts.to p.to x.to


@[simp]
def Term.size : Term -> Nat
| var _ => 0
| defn _ => 0
| spctor _ _ _ t2 =>
  let t2' : Fun.Vec _ _ := size <$> t2
  Vec.sum t2'.to + 1
| ctor0 _ => 0
| ctor1 _ t => size t + 1
| ctor2 _ t1 t2 => size t1 + size t2 + 1
| tbind _ _ t => size t + 1
| lam _ t => size t + 1
| cast _ t1 t2 => size t1 + size t2 + 1
| mtch _ _ t1 _ t3 =>
  let t1' : Fun.Vec _ _ := size <$> t1
  let t3' : Fun.Vec _ _ := size <$> t3
  Vec.sum t1'.to + Vec.sum t3'.to + 1

@[simp]
instance instSizeOf_Term : SizeOf Term where
  sizeOf := Term.size

protected def Term.repr (p : Nat) : (a : Term) -> Std.Format
| .var n => "#" ++ Nat.repr n
| .defn n => "d#" ++ n
| spctor _ _ _ _ => "don't care"
| .ctor0 (.refl t) => Std.Format.paren ("refl! " ++ Ty.repr max_prec t)
| .ctor0 .fail => "fail!"
| .ctor1 (.prj n) t => "(prj! " ++ Nat.repr n ++ " " ++ Term.repr p t ++ ")"
| .ctor1 (.appt τ) t => Repr.addAppParen (Term.repr max_prec t ++ " •[" ++ repr τ ++ "]") p
| .ctor2 .app t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++ " • " ++Term.repr p t2) p
-- | .ctor2 (.app .open) t1 t2 =>
--   Repr.addAppParen (Term.repr max_prec t1 ++ " ∘" ++ Std.Format.sbracket (Term.repr p t2)) p
-- | .ctor2 .cast t1 t2 =>
--   Repr.addAppParen ((Term.repr max_prec t1 ++ " • " ++ Term.repr p t2)) p
| .ctor2 .apptc t1 t2 =>
  Repr.addAppParen (Term.repr max_prec t1 ++
  Std.Format.line ++ " •c" ++ Std.Format.sbracket (Term.repr p t2)) p
| .tbind .lamt K t =>
  Repr.addAppParen ("Λ" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .tbind .allc K t =>
  Repr.addAppParen ("∀c" ++ Std.Format.sbracket (repr K) ++ " " ++ Term.repr max_prec t) p
| .lam τ t => Repr.addAppParen ("λ" ++ Std.Format.sbracket (repr τ) ++ " " ++ Term.repr max_prec t) p
| .cast _ _ _ => "don't care"
| .mtch _ _ _ _ _ => "don't care"
  -- let ts : Vec n Std.Format := λ i =>
  --   let t := ts i
  --   let pat := pats i
  --   Std.Format.nest 4 <| Std.Format.line ++ Term.repr p pat ++ " => " ++ Term.repr p t
  -- let css := Vec.fold Std.Format.nil (·++·) ts
  -- Std.Format.nest 4 <| (("match " ++ Term.repr max_prec s ++ " with")
  --   ++ css
  --   ++ (Std.Format.nest 4 <| Std.Format.line ++ " _ => " ++ Term.repr p allc)
  --   )

@[simp]
instance instRepr_Term : Repr Term where
  reprPrec a p := Term.repr p a
end Core
