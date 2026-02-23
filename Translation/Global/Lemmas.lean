import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
  Surface.GlobalWf G g ->
  ∃ G' g',
    G.translate = some G' ∧
    g.translate G' = some g'  ∧
    Core.GlobalWf G' g' := by
intro h1; induction g <;> simp at *
cases h1

sorry

theorem Translation.ListGlobalWf.sound_isSome :
  ⊢s G ->
  G.translate.isSome
:= by
  sorry

theorem Translation.ListGlobalWf.wf_preserved :
  ⊢s G ->
  G.translate = some G' ->
  ⊢ G'
:= by
  sorry

theorem Translation.ListGlobalWf.sound2 {G : Surface.GlobalEnv} :
  ⊢s G ->
  ∃ G', G.translate = some G' ∧
  ⊢ G'
:= by
  intro wf
  have lem := sound_isSome wf
  generalize zdef : G.translate = z at *
  cases z <;> simp at lem; case _ v =>
  exists v; apply And.intro rfl
  apply wf_preserved wf zdef

-- theorem Translation.ListGlobalWf.sound {G : Surface.GlobalEnv} :
--   ⊢s G ->
--   ∃ G', G.translate = some G' ∧
--   ⊢ G' := by
-- intro wf; induction G <;> simp at *
-- apply Core.ListGlobalWf.nil
-- case cons hd tl ih =>
--   cases wf; case _ wftl wfh =>
--   generalize tldef : Surface.GlobalEnv.translate tl = tl' at *;
--   cases tl' <;> simp at *
--   case none => apply ih wftl
--   case some tl' =>
--     apply Exists.intro _


--     -- generalize gdef : Surface.Ty.translate (Core.Global.data hd.2 hd.3.translate Vect.nil :: tl') [] (hd.4 i).snd = g' at *
--     -- simp [Surface.Ty.translate, List.mapM_cons];
--     sorry
