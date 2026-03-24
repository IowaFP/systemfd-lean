import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas
import Translation.Global
import Core.Metatheory.Determined.Semantic
-- theorem Translation.Ty.ValidCtor :
--   Surface.ValidCtor x T -> Core.ValidCtor x ⟦T⟧ := by
-- intro h; induction h <;> simp at *
-- case base h1 h2 =>
--   replace lem := Translation.Ty.Spine h2 rfl
--   rcases lem with ⟨_, lem⟩
--   constructor; assumption
-- case all ih => apply Core.ValidCtor.all ih
-- case arrow ih => apply Core.ValidCtor.arrow ih

-- theorem Translation.Global.empty_data_wkn {G : Surface.GlobalEnv} {G' : Core.GlobalEnv} (x : String) (K : Surface.Kind) :
--   G.translate = G' ->
--   Surface.GlobalEnv.translate (.data x K Vect.nil :: G) = (.data 0 x ⟦K⟧ Vect.nil :: G') := by
-- intro h; simp [Surface.GlobalEnv.translate]; exact h

-- theorem Surface.GlobalEnvWf.empty_data_wkn x K :
--   ⊢s G -> lookup x G = none ->
--   ⊢s (Surface.Global.data x K Vect.nil :: G) := by
--  intro wf lk; apply ListGlobalWf.cons
--  · apply GlobalWf.data <;> try simp at *
--    apply Vect.nil
--    apply lk
--  · assumption

-- theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
--   ⊢s G ->
--   Surface.GlobalWf G g ->
--   G.translate = G' ->
--   ⊢ G' ->
--  ∃ g',
--     g.translate = g'  ∧
--     Core.GlobalWf G' g' := by
-- intro wf h1 h2 h3; induction g <;> simp at *
-- cases h1
-- case _ n x K ctors cns lk cnsdef ctor_trans =>
-- let ctors' : Vect n (String × Core.Ty) := Surface.Ty.translate_ctors ctors
-- apply Core.GlobalWf.data
-- · intro i y T e;
--   replace ctor_trans := ctor_trans i (ctors i).fst (ctors i).snd rfl;
--   rcases ctor_trans with ⟨k1, k2, k3, k4⟩
--   rcases e with ⟨e1, e2⟩;
--   have lemG := Translation.Global.empty_data_wkn x K h2
--   have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
--   have lem := Translation.Ty.sound wfG (G := .data x K Vect.nil :: G) ⟨k1,lemG, rfl⟩
--   apply And.intro
--   · rcases lem with ⟨K', T', e1, e2, e3⟩;
--     simp at e1; subst e1; subst e2; simp [Surface.KindEnv.translate] at e3; apply e3
--   · apply And.intro
--     · apply Translation.Ty.ValidCtor k2
--     · apply And.intro; assumption
--       apply Translation.GlobalEnv.lookup_none_sound _ h2 k4
-- · assumption
-- · apply Translation.GlobalEnv.lookup_none_sound _ h2 lk


-- theorem Translation.GlobalEnv.wf_sound {G : Surface.GlobalEnv} :
--   ⊢s G ->
--   ⊢ G.translate
-- := by
-- intro wf
-- induction G <;> simp at *
-- case _ => apply Core.ListGlobalWf.nil
-- case _ g gs ih =>
-- cases wf; case _ wfgs wfg =>
-- replace ih := ih wfgs
-- have lem := Translation.GlobalWf.sound wfgs  wfg rfl ih
-- rcases lem with ⟨g', lem1, lem2⟩; subst g'
-- cases g; simp [Surface.Global.translate] at lem2;
-- apply Core.ListGlobalWf.cons _ ih
-- simp; apply lem2

theorem Translation.ValidOpenKind.Sound {K : Surface.Kind}:
  Surface.ValidOpenKind K -> Core.ValidOpenKind K.translate := by
  intro h
  induction h <;> simp at *
  constructor
  constructor; assumption

theorem Surface.Global.Elab.sound :
  ⊢s G ->
  G -↪ G' ->
  ⊢ G' ∧ Core.Global.Determined G' := by
intro wf h
induction h
case nil =>
  apply And.intro
  · apply Core.ListGlobalWf.nil;
  · simp [Core.Global.Determined, Core.Determined.openm, Core.Determined.defn, Core.lookup];
case defn t T t' x j0 jdef ih =>
  cases wf; case _ wfh wftl =>
  replace ih := ih wfh
  cases wftl; case _ lk j1 j2 =>
  replace j1 := Translation.Ty.sound j1 j0 rfl
  rcases j1 with ⟨K, T', e1, e2, j1⟩
  subst e1; cases e2; simp at j1;
  replace j2 := Translation.Term.Sound2 j0 jdef [] [] rfl rfl
  apply And.intro
  · apply Core.ListGlobalWf.cons _ ih.1
    apply Core.GlobalWf.defn j1 j2.2
    · apply Translation.GlobalEnv.lookup_none_sound x j0 lk
  · sorry
case data wf =>
  cases wf; case _ wfh wftl =>
  replace wf := wf wfh
  cases wftl; case _ G G' x K n ctors _ j0 ctors'def lk h1 h2 =>
  apply And.intro
  · apply Core.ListGlobalWf.cons _ wf.1;
    apply Core.GlobalWf.data
    · intro i y T h1;
      simp [ctors'def] at h1; rcases h1 with ⟨h1a, h1b⟩
      replace h2 := h2 i (ctors i).fst (ctors i).snd rfl;
      rcases h2 with ⟨h2a, h2b, h2c, h2d⟩
      have wkn_j0 : Elab (.data x K Vect.nil :: G) (.cons (.data 0 x K.translate Vect.nil) G') := by
        apply Elab.data j0; simp
      replace h2a := Translation.Ty.sound h2a wkn_j0 rfl
      rcases h2a with ⟨_, _, e1, e2, h2a⟩; subst e1; subst e2
      subst y; subst T
      replace h2d := Translation.GlobalEnv.lookup_none_sound (ctors i).fst j0 h2d
      grind
    · intro i j; simp [ctors'def]; apply h1
    · apply Translation.GlobalEnv.lookup_none_sound x j0 lk
  · sorry
case classDecl wf =>
  cases wf; case _ wfh wftl =>
  replace wf := wf wfh
  cases wftl; case _ G G' x K n ms ms' j0 ms'def lk h1 h2 h3 =>
  have wkn_j0 : Elab (.cons (.classDecl x K Vect.nil) G) (.cons (.opent x K.translate) G') := by
    apply Elab.classDecl (x := x) (K := K) (ms := Vect.nil) (ms' := Vect.nil) j0; simp
  apply And.intro
  · simp;
    revert ms'; revert ms; intro ms; apply ms.induction
    case _ =>
      simp; intro ms'
      apply Core.ListGlobalWf.cons _ wf.1;
      apply Core.GlobalWf.opent
      apply Translation.ValidOpenKind.Sound h1
      apply Translation.GlobalEnv.lookup_none_sound x j0 lk
    case _ =>
      simp; intro n mthname mthTy ms ih1 ih2 ih3
      generalize mdef : (Vect.fold [] List.cons fun i =>
        Core.Global.openm ( Vect.cons (mthname, mthTy) ms i).fst ⟦(Vect.cons (mthname, mthTy) ms i).snd⟧) = ms' at *


    --   intro n hd tl wftl
    --   simp; apply Core.ListGlobalWf.cons _ wftl;

      sorry
  sorry
