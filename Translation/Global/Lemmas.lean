import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas
import Translation.Global
import Core.Metatheory.Determined.Semantic

theorem Translation.ValidOpenKind.Sound {K : Surface.Kind}:
  Surface.ValidOpenKind K -> Core.ValidOpenKind K.translate := by
  intro h
  induction h <;> simp at *
  constructor
  constructor; assumption

theorem Surface.Global.Elab.sound :
  G -↪ G' ->
  ⊢ G' ∧ Core.Global.Determined G' := by
intro h
induction h
case nil =>
  apply And.intro
  · apply Core.ListGlobalWf.nil;
  · simp [Core.Global.Determined, Core.Determined.openm, Core.Determined.defn, Core.lookup];
case defn x T t t' j0 lk j1 j2 ih =>
  replace j1 := Translation.Ty.sound j1 j0 rfl
  rcases j1 with ⟨K, T', e1, e2, j1⟩; subst e1; subst e2
  replace j2 := Translation.Term.Sound j0 j2 [] [] rfl rfl
  apply And.intro
  · apply Core.ListGlobalWf.cons _ ih.1
    apply Core.GlobalWf.defn j1 j2.2
    apply Translation.GlobalEnv.lookup_none_sound x j0 lk
  · sorry

case data G G' x K n ctors ctors' j0 h1 h2 h3 ctors'def ih  =>
  apply And.intro
  · apply Core.ListGlobalWf.cons _ ih.1;
    apply Core.GlobalWf.data
    · intro i y T h1';
      simp [ctors'def] at h1'; rcases h1' with ⟨h1a, h1b⟩
      replace h1 := h1 i (ctors i).fst (ctors i).snd rfl;
      rcases h1 with ⟨h2a, h2b, h2c, h2d⟩
      have wkn_j0 : Elab (.data x K Vect.nil :: G) (.cons (.data 0 x K.translate Vect.nil) G') := by
        apply Elab.data j0; simp; simp; apply h3; simp

      replace h2a := Translation.Ty.sound h2a wkn_j0 rfl
      rcases h2a with ⟨_, _, e1, e2, h2a⟩; subst e1; subst e2
      subst y; subst T
      replace h2d := Translation.GlobalEnv.lookup_none_sound (ctors i).fst j0 h2d
      grind
    · intro i j; simp [ctors'def]; apply h2
    · apply Translation.GlobalEnv.lookup_none_sound x j0 h3
  · sorry
case classDecl G G' x K n ms ms' j0 h1 h2 h3 h4 ms'def ih =>
  have wkn_j0 : Elab (.cons (.classDecl x K Vect.nil) G) (.cons (.opent x K.translate) G') := by
    apply Elab.classDecl (x := x) (K := K) (ms := Vect.nil) (ms' := Vect.nil) _ _
    apply h2
    simp
    simp
    simp
    apply j0
    apply h1
  apply And.intro
  · simp; revert ms'; revert ms; intro ms
    apply ms.induction
    case nil =>
      simp; intro ms'
      apply Core.ListGlobalWf.cons _ ih.1
      apply Core.GlobalWf.opent
      apply Translation.ValidOpenKind.Sound h2
      apply Translation.GlobalEnv.lookup_none_sound x j0 h1
    case cons =>
      intro n hd tl h1 h2 h3 ms' ms'def
      replace ms'def := Vect.map_cons ms'def (f := λ (x : String × Ty) => Core.Global.openm x.1 x.2.translate)
      rw[ms'def]; simp;
      apply Core.ListGlobalWf.cons _ _
      · sorry
      · apply h1
        sorry
        sorry
        rfl


    -- apply Core.ListGlobalWf.cons _ ih.1
    -- · apply Core.GlobalWf.classDecl
    --   · sorry
    --   · sorry
    --   · sorry
    --   · sorry
  · sorry
--   cases wf; case _ wfh wftl =>
--   replace wf := wf wfh
--   cases wftl; case _ G G' x K n ms ms' j0 ms'def lk h1 h2 h3 =>
--   have wkn_j0 : Elab (.cons (.classDecl x K Vect.nil) G) (.cons (.opent x K.translate) G') := by
--     apply Elab.classDecl (x := x) (K := K) (ms := Vect.nil) (ms' := Vect.nil) j0; simp
--   apply And.intro
--   · simp;
--     revert ms'; revert ms; intro ms; apply ms.induction
--     case _ =>
--       simp; intro ms'
--       apply Core.ListGlobalWf.cons _ wf.1;
--       apply Core.GlobalWf.opent
--       apply Translation.ValidOpenKind.Sound h1
--       apply Translation.GlobalEnv.lookup_none_sound x j0 lk
--     case _ =>
--       simp; intro n mthname mthTy ms ih1 ih2 ih3
--       generalize mdef : (Vect.fold [] List.cons fun i =>
--        Core.Global.openm ( Vect.cons (mthname, mthTy) ms i).fst ⟦(Vect.cons (mthname, mthTy) ms i).snd⟧) = ms' at *
--       have lem :
--         (Vect.fold [] List.cons fun i => Core.Global.openm (Vect.cons (mthname, mthTy) ms i).fst ⟦(Vect.cons (mthname, mthTy) ms i).snd⟧) =
--           List.cons (Core.Global.openm mthname mthTy.translate) (Vect.fold [] List.cons (fun i => Core.Global.openm (ms i).fst ⟦(ms i).snd⟧)) := by sorry

--     --   intro n hd tl wftl
--     --   simp; apply Core.ListGlobalWf.cons _ wftl;

--       sorry
--   sorry
