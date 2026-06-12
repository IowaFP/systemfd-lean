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

theorem spine_kinding_sound :
  spine_kinding G v x spTy = some () ->
  SpineKinding v x G spTy
:= by

sorry


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
  have lem' := Vec.eq_sound' h7;

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

theorem query_match_sound : query_match q ps = some () -> Query.Match q ps := by
intro h
fun_induction query_match <;> simp at *
case _ a => cases a; apply VecTyping.nil
case _ y _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h3⟩
  apply VecTyping.cons
  simp at h3; exists y.2.1; exists y.2.2.1; exists y.2.2.2; subst h3; rfl
  apply ih h2

theorem pattern_exhaustive_sound {G : GlobalEnv} {ps : Vec (Pattern m) k} {q : Vec String m} {S : Vec Ty m} :
  Query G DataConst.cls q S ->
  check_exhaustive G S ps = some ⟨ℓ, ⟨ref_matrix, idxs⟩⟩ ->
  ∃ i : Fin k, Query.Match q ps[i]
:= by
intro h1 h2
have lem := check_exhaustive_sound h1 h2
unfold check_exhaustive at h2; simp at h2;
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨ref_matrix, h4, h2⟩
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨idxs, h6, h2⟩
replace h6 := Vec.map_seq_sound _ h6
cases h2;
rcases lem with ⟨j, lem⟩
replace h6 := h6 j;
replace h6 := Vec.findIdx_sound h6; simp at h6;
exists idxs.to j
rw[<-lem]; rw[Vec.to_get_elem (vs := idxs)]
apply pattern_match_rfl.1 h6


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
  rcases h5 with ⟨h5, e⟩; subst e
  replace h5 := Vec.eq_sound_lem h5; subst Ks
  replace h12 := Vec.eq_sound_lem h12
  apply Typing.spctor (R := h1.2.2.2.snd) (Ts := h1.2.2.2.1) (Ks := h1.2.1) (Ts' := Ts')
  · rw[h2]
  · apply Eq.symm h12
  · apply Eq.symm h
  · intro i; replace h4 := Vec.map_seq_sound _ h4 i; replace h4 := infer_kind_sound h4;
    simp[instGetElem_Vec]; apply h4
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
  replace h5 := Vec.eq_sound_lem h5; subst Ks
  replace h12 := Vec.eq_sound_lem h10
  apply Typing.spctor (R := h1.2.2.2.snd) (Ts := h1.2.2.2.1) (Ks := h1.2.1) (Ts' := Ts')
  · rw[h2]
  · apply Eq.symm h12
  · apply Eq.symm h11
  · intro i; replace h4 := Vec.map_seq_sound _ h4 i; replace h4 := infer_kind_sound h4;
    simp[instGetElem_Vec]; apply h4
  · intro i; replace h7 := Vec.seq_sound1 _ h7 i;
    apply ih i; simp[instGetElem_Vec]; rw[Vec.to_get_elem] at h7; apply h7
  · intro c e; cases e
  · intro e i; cases e; replace h9 := Vec.map_seq_sound _ h9 i;
    have lem := Vec.units h8 i; rw[lem] at h9
    replace h9 := data_valid_sound _ h9; simp[instGetElem_Vec];
    apply h9

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
    rw[Vec.to_get_elem]
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
    rw[Vec.to_get_elem, h11] at h10; apply h10
  · rw[<-Fun.Vec.to_iso (v := S)] at h8; intro q qs;
    have lem := pattern_exhaustive_sound qs h8
    rcases lem with ⟨i, lem⟩
    exists i; rw[Fun.Vec.to_get_elem ps]; apply lem

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

case _ ih => -- prj[0]
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨AB, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨CD, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h11, h12, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h13, h14, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h15, h16, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h17, h18, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h19, h20, h⟩
  simp at h;
  rcases h with ⟨⟨⟨⟨⟨ e5, e6  ⟩, e4⟩, e3⟩, e2⟩ , e1⟩
  subst e5; subst h13; subst T
  replace h4 := Ty.is_eq_some_sound h4; subst h1
  replace h6 := Ty.is_app_some_sound h6
  replace h8 := Ty.is_app_some_sound h8
  rw[<-Prod.eta h17] at h18
  replace h18 := Kind.is_arrow_sound h18
  subst h9
  rw[<-Prod.eta h19] at h20
  replace h20 := Kind.is_arrow_sound h20
  subst h11
  apply Typing.prj
  · apply ih h2
  · rw[h6, h8, e2]; rw[e2] at h10
    apply CoercionProject.fst_app
    · apply infer_kind_sound h10

case _ ih => -- prj[1]
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨AB, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨CD, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h11, h12, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h13, h14, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h15, h16, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h17, h18, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h19, h20, h⟩
  simp at h;
  rcases h with ⟨⟨⟨⟨⟨ e5, e6  ⟩, e4⟩, e3⟩, e2⟩ , e1⟩
  subst T; subst h13; subst h15
  rw[e2] at e3;
  replace h4 := Ty.is_eq_some_sound h4; subst h1
  replace h6 := Ty.is_app_some_sound h6
  replace h8 := Ty.is_app_some_sound h8
  replace h18 := Kind.is_arrow_sound h18; subst h18
  replace h20 := Kind.is_arrow_sound h20; subst h11
  apply Typing.prj
  · apply ih h2
  · rw[h6, h8];
    apply CoercionProject.snd_app
    · apply infer_kind_sound h14

case _ ih1 ih2 => -- f •c[a]
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h11, h12, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h13, h14, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h15, h16, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h17, h18, h⟩
  simp at h
  rcases h with ⟨⟨e1, e2⟩, e3⟩; rw[e1] at e2; subst T
  replace h6 := Ty.is_eq_some_sound h6; subst h1
  replace h8 := Kind.base_kind_sound _ h8; rw[h8] at h2; rw[h8] at h4
  replace h10 := Ty.is_all_some_sound h10; rw[h10] at h2; rw[h10] at h4
  replace h12 := Ty.is_all_some_sound h12; rw[h12] at h2; rw[h12] at h4
  replace h18 := Ty.is_eq_some_sound h18; subst h18
  rw[e1] at h2; rw[e2] at h16; rw[e2] at h14
  apply Typing.apptc
  · apply ih1 h2
  · apply ih2 h14
  · rfl
  · rfl


case _ ih1 ih2 => -- f • a
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h9, h10, h⟩
  simp at h; rcases h with ⟨e1, e2⟩
  subst T; subst h5
  replace h4 := Ty.is_arrow_some_sound h4; subst h1
  replace h10 := Kind.base_kind_sound _ h10; subst h7
  apply Typing.app
  · apply ih1 h2
  · apply ih2 h6


case _ ih => -- Λ[K]t
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨T, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  cases h
  replace h6 := Kind.base_kind_sound _ h6; subst h3
  rw[Option.bind_eq_some_iff] at h4; rcases h4 with ⟨h7, h8, h4⟩
  simp at h4; subst h7
  apply Typing.lamt
  · apply Kinding.all
    · apply infer_kind_sound h8
  · replace ih := ih h2; simp at ih; apply ih

case _ ih => -- ∀c[K]t
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  cases h
  replace h4 := Ty.is_eq_some_sound h4
  subst h1
  replace h6 := Kind.base_kind_sound _ h6
  rw[h6]; rw[h6] at h2
  apply Typing.allc
  · apply ih h2


end Core
