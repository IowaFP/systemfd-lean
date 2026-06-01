import Core.Infer.Kind
import Core.Infer.KindSound
import Core.Infer.«Type»
import Core.Ty
import Core.Typing
import LeanSubst

import Core.Vec
import Lilac
open Lilac
open LeanSubst


namespace Core

theorem pattern_binders_sound :
  pattern_binders G Δ m Ts p = some Γ ->
  PatternBinders G Δ m Ts p Γ := by
intro h
induction m generalizing Γ <;> simp at *
case _ =>
  cases Ts; cases p; cases h
  apply PatternBinders.zero
case _ n ih =>
  cases Ts; case _ T S =>
  cases p; case _ p ps' =>
  unfold pattern_binders at h;
  simp at h;
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  simp at h; rcases h with ⟨h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Ks, h6, h⟩; simp at h
  rcases h with ⟨h7, h8, h9⟩
  replace ih := @ih _ _ Γ' h2
  replace h6 := Vec.seq_sound h6
  simp only [<-h5.2] at Ks
  simp [SpineTy] at h3;
  let Ts := h3.2.2.2.fst
  let Ts'' := Vec.map (fun T => T[Sequ.append_vec (Vec.map LeanSubst.su p.2.2.fst) +0:_]) Ts
  let R := h3.2.2.2.2
  let As := p.2.2.fst
  rw[<-h5.2] at As
  let R' := R[Sequ.append_vec (Vec.map su As) +0:Ty]
  generalize c_def : p.fst = c at *
  let na := p.2.fst
  let na' := h3.1
  let nb := p.2.2.2
  let nb' := h3.2.2.1
  let h := @PatternBinders.succ G Δ h3.snd.snd.1 c h3.1 Ks (S := S) (p := ps') (ℓ := Γ') (R := R) (As := As) (R' := R') (Ts := Ts) (Ts' := Ts'') n
    (by have lem : Ks = h3.2.1 := by sorry
        rw[h4]; simp[Ts, R, lem])
    (by intro i; rw[h5.2] at i; replace h6 := h6 i; sorry)
    (by unfold Ts''; sorry)
    (by unfold R'; rfl) ih
  subst h9; subst h8;
  simp at h; unfold R' at h; unfold R at h

  sorry





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
