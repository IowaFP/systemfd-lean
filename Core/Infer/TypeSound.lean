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
  have lem' := Vec.eq_sound h7;

  replace h6 := Vec.seq_sound_get_elem h6
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
        simp[h4, Ts, R, lem])
    (by intro i; rw[h5.2] at i; replace h6 := h6 i; sorry)
    (by unfold Ts''; sorry)
    (by unfold R'; rfl) ih
  subst h9; subst h8;
  simp at h; unfold R' at h; unfold R at h

  sorry

theorem query_match_sound : query_match qs ps = some () -> Query.Match qs ps := by
intro h
fun_induction query_match <;> simp at *
case _ a => cases a; apply VecTyping.nil
case _ y _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h3⟩
  apply VecTyping.cons
  simp at h3; exists y.2.1; exists y.2.2.1; exists y.2.2.2; subst h3; rfl
  apply ih h2

theorem pattern_exhaustive_sound (G : GlobalEnv) : (q : Vec String m) -> Query G DataConst.cls q S ->
  check_exhaustive G S ps = some () -> ∃ i, Query.Match q (ps i) := by sorry


theorem data_valid_sound (G : GlobalEnv) :
  Ty.valid_data c G T = some () ->
  T.data? c G := by
intro h
induction T <;> simp at *
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h;
  simp [Ty.data?, Ty.HeadVariable];
  exists h1.fst
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h;
  simp [Ty.data?, Ty.HeadVariable];
  exists h1.fst
  apply And.intro
  · exists h1.2;
  · apply h
case _ a h _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h;
  simp [Ty.data?, Ty.HeadVariable];
  exists h1.1
  replace h2 := Ty.Spine.app_eq.1 h2;
  rcases h2 with ⟨w, h2, h3⟩;
  apply And.intro
  · exists w ++ [a]; exists w;
  · apply h

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

case _ As _ ih => -- spctor
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Ks, h4, h⟩; simp at h
  rcases h with ⟨h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Ts', h7, h⟩; simp at h
  rcases h with ⟨h8, h⟩
  rcases h8 with ⟨h9, h10⟩
  rcases h9 with ⟨h11, h12⟩
  subst h10;
  apply Typing.spctor (R := h1.2.2.2.snd) (Ts := h1.2.2.2.1) (Ks := Ks) (Ts' := Ts')
  · sorry
  · sorry
  · apply Eq.symm h
  · intro i; replace h4 := Vec.map_seq_sound _ h4 i; replace h4 := infer_kind_sound h4;
    simp[instGetElem_Vec]; rw[Vec.to_get_elem Ks, Vec.to_get_elem As] at h4; apply h4
  · intro i; replace h7 := Vec.seq_sound1 _ h7 i;
    apply ih i; simp[instGetElem_Vec]; rw[Vec.to_get_elem] at h7; apply h7
  · intro c e; cases e; apply h11
  · intro h; cases h


case _ As _ ih => -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Ks, h4, h⟩
  simp at h; rcases h with ⟨h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Ts', h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h8, h9, h⟩
  simp at h; rcases h with ⟨h10, h11⟩
  rcases h10 with ⟨h10, e⟩; subst e
  rcases h5 with ⟨h5, e⟩; subst e
  apply Typing.spctor (R := h1.2.2.2.snd) (Ts := h1.2.2.2.1) (Ks := Ks) (Ts' := Ts')
  · sorry
  · sorry
  · apply (Eq.symm h11)
  · intro i; replace h4 := Vec.map_seq_sound _ h4 i; replace h4 := infer_kind_sound h4;
    simp[instGetElem_Vec]; rw[Vec.to_get_elem Ks, Vec.to_get_elem As] at h4; apply h4
  · intro i; replace h7 := Vec.seq_sound1 _ h7 i;
    apply ih i; simp[instGetElem_Vec]; rw[Vec.to_get_elem] at h7; apply h7
  · intro c e; cases e
  · intro e i; cases e; replace h9 := Vec.map_seq_sound _ h9 i;
    have lem := Vec.units h8 i; rw[lem] at h9
    replace h9 := data_valid_sound _ h9; simp[instGetElem_Vec];
    rw[Vec.to_get_elem] at h9; apply h9


case _ m n ss ps ts smτs ih1 ih2 => -- match
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨S, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨ξ, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h11⟩
  apply Typing.mtch (m := m) (n := n) (S := S.to) (ξ := ξ.to)
  · intro i; unfold smτs at h2; replace h2 := Vec.seq_sound1 _ h2;
    apply ih1 i (T := S.to i) (h2 i);
  · intro i; replace h4 := Vec.map_seq_sound _ h4 i;
    have lem := Vec.units h3 i; rw[lem] at h4
    apply data_valid_sound _ h4
  · intro i; replace h6 := Vec.seq_sound1 _ h6 i;
    apply pattern_binders_sound;
    rw[<-Fun.Vec.to_iso (v := S)] at h6; apply h6
  · intro i; replace ih2 := ih2 ξ;
    replace ih2 := ih2 (T := T) i
    rw[Vec.get_elem_indexing (vs := ξ)]
    apply ih2
    replace h10 := Vec.seq_sound2 _ h10 i;
    replace h11 := Vec.get_elem_if_eq_sound h11 i
    rw[<-Vec.get_elem_indexing] at h11; rw [h11] at h10; apply h10
  · intro q qs; apply pattern_exhaustive_sound G q qs h8

case _ ih1 ih2 => -- cast
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨K, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h⟩
  simp at h; rcases h with ⟨h10, h11⟩
  subst h11; subst h10
  replace h8 := Kind.base_kind_sound K h8; subst h8
  replace h4 := Ty.is_eq_some_sound h4; subst h1
  apply Typing.cast
  · replace h6 := infer_kind_sound h6
    apply h6
  · apply ih1 h2
  · apply ih2 h10
  · rfl

case _ ih => -- lam
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨B, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h6, h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h8, h9, h⟩
  cases h;
  replace h9 := Kind.base_kind_sound _ h9; subst h6
  replace h4 := Kind.base_kind_sound _ h4; subst h1
  apply Typing.lam
  · apply infer_kind_sound h2
  · apply ih h6

case _ => -- refl
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  cases h
  apply Typing.refl
  · apply infer_kind_sound h2

case _ ih => -- t •[T]
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  simp at h; rcases h with ⟨h6, h7⟩
  subst h1; subst T
  replace h6 := Ty.is_all_some_sound h6; subst h3
  apply Typing.appt
  · apply ih h4
  · apply infer_kind_sound h2
  · rfl

sorry
sorry
sorry
sorry
sorry
sorry

end Core
