import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas
import Translation.Global

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
  G.translate = G' ->
  Surface.GlobalEnv.translate (.data x K Vect.nil :: G) = (.data 0 x ⟦K⟧ Vect.nil :: G') := by
intro h; simp [Surface.GlobalEnv.translate]; exact h

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
  G.translate = G' ->
  ⊢ G' ->
 ∃ g',
    g.translate = g'  ∧
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
      apply Translation.GlobalEnv.lookup_none_sound _ h2 k4
· assumption
· apply Translation.GlobalEnv.lookup_none_sound _ h2 lk


theorem Translation.GlobalEnv.wf_sound {G : Surface.GlobalEnv} :
  ⊢s G ->
  ⊢ G.translate
:= by
intro wf
induction G <;> simp at *
case _ => apply Core.ListGlobalWf.nil
case _ g gs ih =>
cases wf; case _ wfgs wfg =>
replace ih := ih wfgs
have lem := Translation.GlobalWf.sound wfgs  wfg rfl ih
rcases lem with ⟨g', lem1, lem2⟩; subst g'
cases g; simp [Surface.Global.translate] at lem2;
apply Core.ListGlobalWf.cons _ ih
simp; apply lem2
