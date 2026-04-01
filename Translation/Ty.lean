import Surface.Ty
import Core.Ty
import Core.Global
import Core.Typing
import Surface.Typing

import LeanSubst
open LeanSubst

namespace Surface

@[simp]
def Kind.translate : Surface.Kind -> Core.Kind
| .base .closed => .base .closed
| .base .open => .base .open
| .arrow k1 k2 => .arrow (translate k1) (translate k2)
notation "⟦" K "⟧" => Surface.Kind.translate K

def KindEnv.translate : Surface.KindEnv -> Core.KindEnv := List.map (·.translate)
notation "⟦" Δ "⟧" => Surface.KindEnv.translate Δ

@[simp]
def Ty.translate: Surface.Ty -> Core.Ty
| .var x => .var x
| .global x => .global x
| .arrow a b => .arrow (a.translate) (b.translate)
| .then a b => .arrow (a.translate) (b.translate)
| .app a b => .app (a.translate) (b.translate)
| .all k p =>
  .all k.translate (p.translate)
notation "⟦" A "⟧" => Surface.Ty.translate A

@[simp]
def TyEnv.translate (Γ : TyEnv) : (List Core.Ty) :=
  Γ.map (·.translate)
notation "⟦" Γ "⟧" => Surface.TyEnv.translate Γ

@[simp]
def Subst.Ty.translate (σ : Subst Surface.Ty) : Subst Core.Ty :=
  (λ x => match x with
  | .re x => .re x
  | .su T => .su (T.translate)) <$> σ
notation "⟦" σ "⟧" => Subst.Ty.translate σ

end Surface

namespace Core

def Ty.monoty : Ty -> Bool
| .all _ _ => false
| _ => true

@[simp]
def Ty.fresh_vars : Nat -> List Nat
| 0 => []
| n + 1 => n :: fresh_vars n

@[simp]
def Ty.mk_arrow (b : Ty) : List Ty -> Ty
| [] => b
| .cons x xs => x -:> Ty.mk_arrow b xs

@[simp]
def Ty.mk_all (b : Ty) : Nat -> Ty
| 0 => b
| n + 1 => ∀[★] (Ty.mk_all b n)

--- C τ1 τ2 ---> ∀ ∀ (1 ~ τ1) (0 ~ τ2)  -> C 0 1
--- but also
--- ∀αs. T βs => C τs ------> ∀
@[simp]
def Ty.InstEncode (τ : Ty) : Option Ty :=
  match τ.spine with
  | .some (x , sp) =>
    let fvs := fresh_vars sp.length
    let prefix_τs := (fvs.zip sp).map (λ (n, τ) => t#n ~[★]~ τ )
    return ((((gt#x).apply (fvs.map (t#·))).mk_arrow prefix_τs).mk_all fvs.length)
  | _ => none

#eval Ty.InstEncode ((gt#"C").apply [gt#"a", gt#"b"] )


def Ty.Apart : Ty -> Ty -> Bool
| t#_, _ => false
| _ , t#_ => false
| gt#x , gt#y => x != y
| gt#_, _ => true
| .app τ1 a , .app τ2 b => τ1.Apart τ2 && a.Apart b
| .app _ _, _ => true
| .arrow τa1 τb1, .arrow τa2 τb2 => τa1.Apart τa2 && τb1.Apart τb2
| .arrow _ _, _ => true
| _ , _ => true

#eval Ty.Apart ((gt#"C").apply [gt#"a", gt#"b"] ) ((gt#"C").apply [gt#"a", gt#"b"] )



theorem Ty.InstEncodeKindSound :
  G&Δ ⊢ τ : ◯ ->
  some τ' = Ty.InstEncode τ  ->
  G&Δ ⊢ τ' : ◯ := by
intro h1 h2
induction τ <;> simp [Ty.spine, Ty.apply] at *
case global => subst h2; apply h1
case app => sorry

end Core
