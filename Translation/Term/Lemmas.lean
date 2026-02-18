import Core.Ty
import Core.Term
import Surface.Ty
import Surface.Term

import Translation.Ty
import Translation.Term

import Translation.Ty.Lemmas

import Translation.Ty
import Translation.Term
import Translation.Global

theorem Translation.Term.Sound :
  G&Δ,Γ ⊢s t : T ->
  trans_global G = some G' ->
  trans_kis Δ = Δ' ->
  trans_tys G' Δ' Γ = some Γ' ->
  trans_ki K = K' ->
  trans_ty G' Δ' T = some T' ->
  trans_term G' Δ' Γ' t = some t' ->
  G'&Δ',Γ' ⊢ t' : T' := by sorry
