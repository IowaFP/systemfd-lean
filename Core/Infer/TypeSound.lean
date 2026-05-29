import Core.Infer.Kind
import Core.Infer.KindSound
import Core.Infer.«Type»
import Core.Ty
import Core.Typing

import Core.Vec
import Lilac
open Lilac

namespace Core

theorem infer_type_sound :
  ⊢ G ->
  t.infer_type G Δ Γ = some T ->
  G&Δ, Γ ⊢ t : T := by
intro wf h
fun_induction Term.infer_type generalizing T <;> simp at *
case _ => -- var
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  cases h
  replace h6 := Kind.base_kind_sound h3 h6; subst h3
  apply Typing.var
  · apply h2
  · apply infer_kind_sound h4

case _ => -- defn
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩; simp at h;
  rcases h with ⟨h5, h6⟩; subst h3; subst T
  replace h4 := infer_kind_sound h4
  apply Typing.defn
  apply h2
  apply h4

case _ ih => -- spctor
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩; simp at h
  rcases h with ⟨h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h6, h7, h⟩; simp at h
  rcases h with ⟨h8, h⟩
  rcases h8 with ⟨h9, h10⟩
  rcases h9 with ⟨h11, h12⟩
  replace h4 := Vec.seq_sound h4
  sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry
sorry

end Core
