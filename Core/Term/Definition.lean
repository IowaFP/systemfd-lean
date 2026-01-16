import LeanSubst
import Core.Ty
import Core.Vec

open LeanSubst

inductive Ctor0Variant : Type where
| zero
| refl (A : Ty)

inductive Ctor1Variant : Type where
| sym
| fst
| snd
| appt (a : Ty)

inductive Ctor2Variant : Type where
| app
| appo
| cast
| seq
| appc
| apptc
| arrowc
| choice

inductive TyBindVariant : Type where
| lamt
| allc

inductive Term : Type where
| var : Nat -> Term
| global : String -> Term
| ctor0 : Ctor0Variant -> Term
| ctor1 : Ctor1Variant -> Term -> Term
| ctor2 : Ctor2Variant -> Term -> Term -> Term
| tbind : TyBindVariant -> Kind -> Term -> Term
| lam : Ty -> Term -> Term
| guard : Term -> Term -> Term -> Term
| «match» : Term -> Term -> Vec Term n -> Term

prefix:max "#" => Term.var
prefix:max "g#" => Term.global

-- ctor0 notation
notation "`0" => Term.ctor0 Ctor0Variant.zero
notation "refl! " A => Term.ctor0 (Ctor0Variant.refl A)

-- ctor1 notation
prefix:max "sym!" => Term.ctor1 Ctor1Variant.sym
notation "fst!" t => Term.ctor1 Ctor1Variant.fst t
notation "snd!" t => Term.ctor1 Ctor1Variant.snd t
notation f " •[" a "]" => Term.ctor1 (Ctor1Variant.appt a) f

-- ctor2 notation
notation f " • " a => Term.ctor2 Ctor2Variant.app f a
notation f " ∘[" a "]" => Term.ctor2 Ctor2Variant.appo f a
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

notation "match!" => Term.match

@[simp]
def Term.size : Term -> Nat
| var _ => 0
| global _ => 0
| ctor0 _ => 0
| ctor1 _ t => size t + 1
| ctor2 _ t1 t2 => size t1 + size t2 + 1
| tbind _ _ t => size t + 1
| lam _ t => size t + 1
| guard t1 t2 t3 => size t1 + size t2 + size t3 + 1
| .match t1 t2 ts => size t1 + size t2 + Vec.sum (λ i => (ts i).size) + 1
