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

theorem Translation.Term.Sound (G : Surface.GlobalEnv) :

  G&Δ,Γ ⊢s t : T ->

  (Surface.Global.translateEnv G = some G' ∧
  Surface.Kind.translateEnv Δ = Δ' ∧
  Surface.Ty.translateEnv G' Δ' Γ = some Γ' ∧
  T.translate G' Δ' = some T' ∧
  t.translate G' Δ' Γ' = some t' ∧
  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T') := by sorry
