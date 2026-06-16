import Core.Infer.KindSound
import Core.Infer.TypeSound
import Core.Infer.Global

import Core.Global

import Core.Vec

open Lilac

namespace Core

theorem wf_global_sound :
  GlobalEnv.wf_globals G = some () ->
  ⊢ G
:= by
intro h
fun_induction GlobalEnv.wf_globals <;> simp at *
case _ =>  -- empty
  apply ListGlobalWf.nil

case _ n x k ctors G ih => -- ctors
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; rcases h with ⟨h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h4, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h6, h7, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h8, h9, h⟩
  replace h5 := Vec.map_seq_sound _ h5
  replace h7 := Vec.map_seq_sound _ h7
  replace h9 := Vec.map_seq_sound _ h9
  replace h4 := Vec.units h4;
  rcases h3 with ⟨h3a, h3b⟩
  apply ListGlobalWf.cons
  · apply GlobalWf.data (G := G) (n := n) (K := k) (x := x) (ctors := ctors)
    · intro i y T h
      apply And.intro
      · replace h5 := h5 i; rw[h] at h5; simp at h5; apply spine_kinding_sound h5
      · apply And.intro
        · replace h7 := h7 i; rw[h] at h7; simp at h7; simp; intro f; apply h7 (Eq.symm f)
        · replace h9 := h9 i; rw[h] at h9; simp at h9; apply h9
    replace h3b := Vec.unique_elems_sound h3b; simp at h3b; apply h3b
    apply h3a
  · apply ih h2

case _ ih =>  -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h;  rcases h with ⟨h3, h⟩
  replace h := spine_kinding_sound h
  replace ih := ih h2
  apply ListGlobalWf.cons
  · apply GlobalWf.openm h h3
  · apply ih

case _ ih =>  -- octor
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; rcases h with ⟨e, h⟩
  apply ListGlobalWf.cons
  · apply GlobalWf.octor
    apply spine_kinding_sound h
    apply e
  · apply ih h2

case _ ih => -- defn
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  simp at h; rcases h with ⟨e1, h⟩; subst e1
  apply ListGlobalWf.cons
  · apply GlobalWf.defn
    · replace h8 := Kind.base_kind_sound _ h8; subst h5
      replace h6 := infer_kind_sound h6; apply h6
    · replace h4 := infer_type_sound (ih h2) h4; apply h4
    · apply h
  · apply ih h2

case _ m _ p t G ih => -- inst
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  split at h
  case _ x n Ks _ Ts R lk =>
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ, h4, h⟩
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨R, h6, h⟩
    simp at h; rcases h with ⟨e1, e2⟩; subst e1; subst e2;
    simp [Vec.length] at *
    replace ih := ih h2
    replace h6 := infer_type_sound ih h6
    have lem := lookup_name_eq lk; simp [Entry.name] at lem; subst lem
    apply ListGlobalWf.cons
    -- · apply GlobalWf.inst (G := G) (Δ := Ks.to_list) (x := x) (n := n) (m := m) (p := p) (t := t)
    --   apply lk
    --   sorry
    --   sorry
    --   sorry
    --   sorry
    --   sorry
    --   sorry
      sorry

    · apply ih
  · cases h

case _ ih => -- odata
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h
  apply ListGlobalWf.cons
  · apply GlobalWf.odata h
  · apply ih h2



theorem open_exhaustive_sound {G : GlobalEnv} :
  G.check_open_exhaustive = some () ->
  OpenExhaustive G
:= by
intro h
unfold OpenExhaustive
intro x na nb τ As Ks Ts Ts' Δ R q lk wk σ h1 h2

unfold GlobalEnv.check_open_exhaustive at h; simp at h
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨n, h, e⟩; cases e
sorry


end Core
