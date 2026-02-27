import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas
import Translation.Global

theorem Translation.Global.is_data_sound x :
  ⊢s G ->
  G.translate = some G' ->
  Surface.is_data G x ->
  Core.is_data G' x := by
sorry

theorem Translation.GlobalEnv.lookup_sound :
  G.translate = some G' ->
  (∀ x, Surface.lookup x G = none -> Core.lookup x G' = none) := by sorry


theorem Translation.Ty.ValidCtor :
  Surface.ValidCtor x T -> Core.ValidCtor x ⟦T⟧ := by
intro h; induction h <;> simp at *
case base h1 h2 =>
  replace lem := Translation.Ty.Spine h2 rfl
  rcases lem with ⟨_, lem⟩
  constructor; assumption
case all ih => apply Core.ValidCtor.all ih
case arrow ih => apply Core.ValidCtor.arrow ih

theorem Translation.Global.empty_data_wkn {G : Surface.GlobalEnv} {G' : Core.GlobalEnv} (x : String) (K : Surface.Kind) :
  G.translate = some G' ->
  Surface.GlobalEnv.translate (.data x K Vect.nil :: G) = some (.data 0 x ⟦K⟧ Vect.nil :: G') := by
intro h; simp [Surface.GlobalEnv.translate]
rw[Option.bind_eq_some_iff]; exists G'

theorem Surface.GlobalEnvWf.empty_data_wkn x K :
  ⊢s G -> lookup x G = none ->
  ⊢s (Surface.Global.data x K Vect.nil :: G) := by
 intro wf lk; apply ListGlobalWf.cons
 · apply GlobalWf.data <;> try simp at *
   apply Vect.nil
   apply lk
 · assumption


theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
  ⊢s G ->
  Surface.GlobalWf G g ->
  G.translate = some G' ->
  ⊢ G' ->
 ∃ g',
    g.translate G' = some g'  ∧
    Core.GlobalWf G' g' := by
intro wf h1 h2 h3; induction g <;> simp at *
cases h1
case _ n x K ctors cns lk cnsdef ctor_trans =>
let ctors' : Vect n (String × Core.Ty) := Surface.Ty.translate_ctors ctors
apply Core.GlobalWf.data
· intro i y T e;
  replace ctor_trans := ctor_trans i (ctors i).fst (ctors i).snd rfl;
  rcases ctor_trans with ⟨k1, k2, k3, k4⟩
  rcases e with ⟨e1, e2⟩;
  have lemG := Translation.Global.empty_data_wkn x K h2
  have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
  have lem := Translation.Ty.sound wfG (G := .data x K Vect.nil :: G) ⟨k1,lemG, rfl⟩
  apply And.intro
  · rcases lem with ⟨K', T', e1, e2, e3⟩;
    simp at e1; subst e1; subst e2; simp [Surface.KindEnv.translate] at e3; apply e3
  · apply And.intro
    · apply Translation.Ty.ValidCtor k2
    · apply And.intro; assumption
      apply Translation.GlobalEnv.lookup_sound h2; apply k4
· assumption
· apply Translation.GlobalEnv.lookup_sound h2 _ lk

theorem Translation.ListGlobalWf.wf_preserved :
  ⊢s G ->
  G.translate = some G' ->
  ⊢ G'
:= by
  intro wf h1; induction wf generalizing G' <;> simp at *
  case nil => subst G'; apply Core.ListGlobalWf.nil
  case cons g wfg wf ih =>
    rw[Option.bind_eq_some_iff] at h1
    rcases h1 with ⟨G', h1, h2⟩; cases h2
    replace ih := ih h1
    have lem := Translation.GlobalWf.sound wf wfg h1 ih
    rcases lem with ⟨g', lem1, lem2⟩
    replace ih := Core.ListGlobalWf.cons lem2 ih
    cases g; simp at *
    subst g'; apply ih


theorem Translation.ListGlobalWf.sound_isSome :
  ⊢s G ->
  G.translate.isSome
:= by
intro wf
induction G using Surface.GlobalEnv.translate.induct <;> simp at *
case _ ih =>
  cases wf; case _ g gs wftl wfg =>
  replace ih := ih wftl
  rw[Option.isSome_iff_exists] at ih
  rcases ih with ⟨gs', ih⟩
  rw[Option.isSome_iff_exists]
  exists (Core.Global.data g.1 g.2 ⟦g.3⟧ (Surface.Ty.translate_ctors g.4) :: gs')
  rw[ih]; simp

theorem Translation.ListGlobalWf.sound {G : Surface.GlobalEnv} :
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
