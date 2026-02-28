import Core.Ty
import Core.Term
import Core.Metatheory.Determined.Definition
import Surface.Ty
import Surface.Term

import Translation.Ty
import Translation.Term

import Translation.Ty.Lemmas

import Translation.Ty
import Translation.Term
import Translation.Global
import Core.Typing
import Surface.BiTyping
import Core.Metatheory.Inversion
import Core.Term.Spine
import Surface.Typing
import Surface.Metatheory.Inversion
import Translation.Rename

open LeanSubst

namespace Surface

theorem Translation.Term.Sound_2d_syn (G : Surface.GlobalEnv) :
  ⊢s G ->
  G&Δ,Γ ⊢s t => T ->


  G.translate = G' ->
  ⊢ G' ->

  Δ.translate = Δ' ->
  Γ.translate = Γ' ->


  ∃ t', t.check_type_translate G' Δ' Γ' = some t' ∧
        t'.Determined ∧
        G'&Δ',Γ' ⊢ t' : T.translate := by sorry



theorem Translation.Term.Sound_2d_chk (G : Surface.GlobalEnv) :
  ⊢s G ->
  G&Δ,Γ ⊢s t <= T ->


  G.translate = G' ->
  ⊢ G' ->

  Δ.translate = Δ' ->
  Γ.translate = Γ' ->


  ∃ t', t.type_directed_translate G' Δ' Γ' T.translate = some t' ∧
        t'.Determined ∧
        G'&Δ',Γ' ⊢ t' : T.translate := by
intro wf j h1 h2 h3 h4

sorry




end Surface
