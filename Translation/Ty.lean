import Surface.Ty
import Core.Ty
import Core.Global
import Core.Typing
import Surface.Typing

import LeanSubst
open LeanSubst

@[simp]
def Surface.Kind.translate : Surface.Kind -> Core.Kind
| .base .closed => .base .closed
| .base .open => .base .open
| .arrow k1 k2 => .arrow (translate k1) (translate k2)
notation "⟦" K "⟧" => Surface.Kind.translate K

def Surface.KindEnv.translate : Surface.KindEnv -> Core.KindEnv := List.map (·.translate)
notation "⟦" Δ "⟧" => Surface.KindEnv.translate Δ

@[simp]
def Surface.Ty.translate: Surface.Ty -> Core.Ty
| .var x => .var x
| .global x => .global x
| .arrow a b => .arrow (a.translate) (b.translate)
| .then a b => .arrow (a.translate) (b.translate)
| .app a b => .app (a.translate) (b.translate)
| .all k p =>
  .all k.translate (p.translate)
notation "⟦" A "⟧" => Surface.Ty.translate A

@[simp]
def Surface.TyEnv.translate (Γ : TyEnv) : (List Core.Ty) :=
  Γ.map (·.translate)
notation "⟦" Γ "⟧" => Surface.TyEnv.translate Γ

@[simp]
def Subst.Surface.Ty.translate (σ : Subst Surface.Ty) : Subst Core.Ty :=
  (λ x => match x with
  | .re x => .re x
  | .su T => .su (T.translate)) <$> σ
notation "⟦" σ "⟧" => Subst.Surface.Ty.translate σ


inductive Surface.Translation.Ty (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) :
  Surface.KindEnv -> Surface.Ty -> Surface.Kind ->
  Core.KindEnv -> Core.Ty -> Core.Kind -> Prop where
| var {Δ : Surface.KindEnv} :
  Δ[i]? = some K ->
  Δ'[i]? = some K.translate ->
  Translation.Ty G G' Δ t`#i K Δ' t#i K.translate
| arrow :
  Translation.Ty G G' Δ A `★ Δ' A' ★ ->
  Translation.Ty G G' Δ B K Δ' B' K.translate ->
  Translation.Ty G G' Δ (A `-:> B) `★ Δ' (A' -:> B') ★
| «then» :
  Translation.Ty G G' Δ A `◯ Δ' A' ◯ ->
  Translation.Ty G G' Δ B K Δ' B' K.translate ->
  Translation.Ty G G' Δ (A `=:> B) `★ Δ' (A' -:> B') ★
| app :
  Translation.Ty G G' Δ A (.arrow K1 K2) Δ' A' (Surface.Kind.arrow K1 K2).translate ->
  Translation.Ty G G' Δ B K1 Δ' B' K1.translate ->
  Translation.Ty G G' Δ (A `• B) K2 Δ' (A' • B') K2.translate
| all :
  Translation.Ty G G' Δ A K Δ' A' K.translate ->
  Translation.Ty G G' (K::Δ) B `★ (K.translate::Δ') B' ★ ->
  Translation.Ty G G' Δ (`∀[K]B) `★ Δ' (∀[K.translate] B') ★
