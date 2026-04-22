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

theorem Surface.Global.ValidClassDecl.sound :
  G -↪ G' ->
  ⊢ G' ->
  ValidClassDecl G G' x K ms Δ ->
  ⊢ Δ ∧ Core.Global.Determined Δ := by
intro h1 h2 h3
induction h3
case nil lk vk =>
  apply And.intro
  · apply Core.ListGlobalWf.cons _ h2
    apply Core.GlobalWf.opent (Translation.ValidOpenKind.Sound vk)
    · apply Translation.GlobalEnv.lookup_none_sound x h1 lk
  · sorry
case cons Δ oms τ ms m T k2 lk k3 k4 k5 ih =>
  apply And.intro
  · apply Core.ListGlobalWf.cons
    apply Core.GlobalWf.openm
    · sorry
    · rw[k2]; simp

      sorry
    · sorry
    apply ih.1
  sorry



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
  replace j1 := Translation.Ty.sound j1 j0
  replace j2 := Translation.Term.Sound j0 j2
  apply And.intro
  · apply Core.ListGlobalWf.cons _ ih.1
    apply Core.GlobalWf.defn j1 j2.2
    apply Translation.GlobalEnv.lookup_none_sound x j0 lk
  · simp[Core.Global.Determined]; intro x
    apply And.intro
    sorry
    sorry

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

      replace h2a := Translation.Ty.sound h2a wkn_j0
      subst y; subst T
      replace h2d := Translation.GlobalEnv.lookup_none_sound (ctors i).fst j0 h2d
      grind
    · intro i j; simp [ctors'def]; apply h2
    · apply Translation.GlobalEnv.lookup_none_sound x j0 h3
  · sorry
case classDecl G G' x K n ms Δ j0 h1 h2 =>
  apply Surface.Global.ValidClassDecl.sound j0 h2.1 h1
case instDecl => sorry
