import Core.Ty
import Core.Term
import Core.Metatheory.Determined
import Surface.Ty
import Surface.Term

import Translation.Ty
import Translation.Term

import Translation.Ty.Lemmas

import Translation.Ty
import Translation.Term
import Translation.Global
import Core.Typing
import Surface.Typing


def Surface.TyEnv.translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Surface.TyEnv) : Option (Core.TyEnv) := Γ.mapM (·.translate G Δ )

theorem Translation.Term.Sound (G : Surface.GlobalEnv) :
  ⊢s G ->
  G&Δ,Γ ⊢s t : T ->
  G.translate = some G' ->
  Δ.translate = Δ' ->
  Γ.translate G' Δ' = some Γ' ->

  (T.translate G' Δ' = some T' ∧
  t.translate G' Δ' Γ' = some t' ∧
  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T') := by

sorry
