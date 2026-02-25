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

def Surface.KindEnv.translate : Surface.KindEnv -> Core.KindEnv := List.map (·.translate)

@[simp]
def Surface.Ty.translate: Surface.Ty -> Core.Ty
| .var x => .var x
| .global x => .global x
| .arrow a b => .arrow (a.translate) (b.translate)
| .app a b => .app (a.translate) (b.translate)
| .all k p =>
  .all k.translate (p.translate)

@[simp]
def Surface.TyEnv.translate (Γ : TyEnv) : (List Core.Ty) :=
  Γ.map (·.translate)

@[simp]
def Subst.Surface.Ty.translate (σ : Subst Surface.Ty) : Subst Core.Ty :=
  (λ x => match x with
  | .re x => .re x
  | .su T => .su (T.translate)) <$> σ


theorem Subst.Surface.Ty.translate_compose {σ : Subst Surface.Ty} :
  Subst.Surface.Ty.translate σ.lift =
    re 0 :: Subst.Surface.Ty.translate σ ∘ +1 := by
funext; simp
case _ x =>
induction x <;> simp at *
case _ x ih => sorry
