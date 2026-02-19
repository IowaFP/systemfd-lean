import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
  Surface.GlobalWf G g ->
  ∃ G' g',
    Surface.Global.translateEnv G = some G' ∧
    g.translate G' = some g'  ∧
    Core.GlobalWf G' g' := by
intro h1; induction g <;> simp at *
cases h1

sorry


theorem Translation.ListGlobalWf.sound {G : List Surface.Global} :
  ⊢s G ->
  ∃ G', Surface.Global.translateEnv G = some G' ∧
  ⊢ G' := by
intro wf; induction G <;> simp at *
apply Core.ListGlobalWf.nil
case cons hd tl ih =>

 sorry
