import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

theorem Translation.Ty.valid_ctor_ty_sound {G : Core.GlobalEnv} :
  Core.is_valid_ctor_ty G T == some () -> ∃ x, Core.ValidCtor x T := by
intro h
fun_induction Core.is_valid_ctor_ty <;> simp at *
case _ ih => replace ih := ih h; rcases ih with ⟨x, ih⟩; exists x; apply Core.ValidCtor.all ih
case _ ih => replace ih := ih h; rcases ih with ⟨x, ih⟩; exists x; apply Core.ValidCtor.arrow ih
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨tnf, h1, h2⟩; exists tnf.1; simp at h2;
  apply Core.ValidCtor.base; apply h1


theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
  ⊢s G ->
  Surface.GlobalWf G g ->
  G.translate = some G' ->
  ⊢ G' ->
 ∃ g',
    g.translate G' = some g'  ∧
    Core.GlobalWf G' g' := by
intro wf h1 h2 wfc; induction g <;> simp at *
cases h1
case _ n x K ctors cns cnsu lk cnsdef ctor_trans =>
let ctors' : Vect n (String × Core.Ty) := sorry --Vect.seq
exists Core.Global.data n x ⟦K⟧ ctors'
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
