import Surface.Term
import Core.Term

-- import Translation.Term
import Translation.Ty
import Surface.Metatheory.Rename
import Core.Metatheory.Rename
import Core.Metatheory.Substitution

open LeanSubst


theorem Translation.Ty.Rename (r : Ren) {T : Surface.Ty}{T' : Core.Ty} :
  T.translate = T' ->
  (T[r]).translate = (T'[r]) := by
intro h1
fun_induction Surface.Ty.translate generalizing T' r <;> (subst h1 ; simp at *)
case _ => simp[Ren.to]
all_goals try (
case _ ih1 ih2 =>
  apply And.intro
  · apply ih1 r
  · apply ih2 r
)
case _ k p ih =>
  replace ih := @ih r.lift
  simp at ih; apply ih

theorem Translation.Ty.Weaken {T : Surface.Ty} {T' : Core.Ty} :
  T.translate = T' ->
  (T[+1]).translate = (T'[+1]) := by
intro h; apply Translation.Ty.Rename (λ x => x + 1) h


theorem Translation.Ty.Subst (σ : Subst Surface.Ty)
  {T : Surface.Ty} {T' : Core.Ty} :
  T.translate = T' ->
  (T[σ]).translate = T'[Subst.Surface.Ty.translate σ] := by
intro h1
fun_induction Surface.Ty.translate generalizing T' σ <;> (subst h1; simp at *)
case _ x =>
  generalize zdef : σ x = z at *
  cases z <;> simp at *
all_goals try (
case _ ih1 ih2 =>
  replace ih1 := ih1 σ
  replace ih2 := ih2 σ
  apply And.intro ih1 ih2
)
case _ k p ih =>
  replace ih := ih σ.lift
  have lem := Subst.Surface.Ty.translate_compose (σ := σ)
  simp at lem ih
  rw[ih, lem]
