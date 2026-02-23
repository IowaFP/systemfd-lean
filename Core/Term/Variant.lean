import LeanSubst
import Core.Term.Definition

open LeanSubst
namespace Core

def Term.not_choice : Term -> Bool
| ctor2 .choice _ _ => false
| _ => true

inductive Variant : Type where
| ctor0 : Ctor0Variant -> Variant
| ctor1 : Ctor1Variant -> Variant
| ctor2 : Ctor2Variant -> Variant
| tbind : TyBindVariant -> Variant
| lam : Variant
| guard : Variant
| mtch : Variant

@[coe]
def Variant.from_ctor0 (c : Ctor0Variant) : Variant := ctor0 c

instance : Coe Ctor0Variant Variant where
  coe := Variant.from_ctor0

@[coe]
def Variant.from_ctor1 (c : Ctor1Variant) : Variant := ctor1 c

instance : Coe Ctor1Variant Variant where
  coe := Variant.from_ctor1

@[coe]
def Variant.from_ctor2 (c : Ctor2Variant) : Variant := ctor2 c

instance : Coe Ctor2Variant Variant where
  coe := Variant.from_ctor2

@[coe]
def Variant.from_tbind (c : TyBindVariant) : Variant := tbind c

instance : Coe TyBindVariant Variant where
  coe := Variant.from_tbind

inductive VariantMissing : List Variant -> Term -> Prop where
| var : VariantMissing vs #x
| global : VariantMissing vs g#x
| ctor0 {c : Ctor0Variant} :
  ↑c ∉ vs ->
  VariantMissing vs (.ctor0 c)
| ctor1 {c : Ctor1Variant} :
  ↑c ∉ vs ->
  VariantMissing vs t ->
  VariantMissing vs (.ctor1 c t)
| ctor2 {c : Ctor2Variant} :
  ↑c ∉ vs ->
  VariantMissing vs t1 ->
  VariantMissing vs t2 ->
  VariantMissing vs (.ctor2 c t1 t2)
| tbind {c : TyBindVariant} :
  ↑c ∉ vs ->
  VariantMissing vs t ->
  VariantMissing vs (.tbind c K t)
| lam :
  VariantMissing vs t ->
  VariantMissing vs (.lam A t)
| guard :
  VariantMissing vs t1 ->
  VariantMissing vs t2 ->
  VariantMissing vs t3 ->
  VariantMissing vs (.guard t1 t2 t3)
| mtch :
  VariantMissing vs t ->
  (∀ i, VariantMissing vs (ps i)) ->
  (∀ i, VariantMissing vs (ts i)) ->
  VariantMissing vs c ->
  VariantMissing vs (.match t ps ts c)
end Core
