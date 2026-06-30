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
  replace h5 := Vec.traverse_eq_pure_iff_getElem h5
  replace h7 := Vec.traverse_eq_pure_iff_getElem h7
  replace h9 := Vec.traverse_eq_pure_iff_getElem h9
  replace h4 := Vec.units h4;
  rcases h3 with ⟨h3a, h3b⟩
  replace h3b := Vec.unique_elems_sound h3b;
  apply ListGlobalWf.cons; simp at h3b
  · apply GlobalWf.data (G := G) (n := n) (K := k) (x := x) (ctors := ctors)
    · intro i y T h
      apply And.intro
      · replace h5 := h5 i; simp at h5;
        replace h5 := spine_kinding_sound h5; simp at h5;
        have lem : ctors[i].1 = y := by rw[h]
        rw[lem] at h5; clear lem;
        have lem : ctors[i].2 = T := by rw[h]
        rw[lem] at h5; apply h5
      · apply And.intro
        · replace h7 := h7 i; rw[h] at h7; simp at h7; simp; intro f; apply h7 (Eq.symm f)
        · replace h9 := h9 i; rw[h] at h9; simp at h9; apply h9
    · apply h3b
    · apply h3a
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
  case _ x _ _ _ Ks1 _ Ks2 _ Ts R lk =>
    simp at h; rcases h with ⟨⟨e1, e2⟩, h⟩; subst e1; subst e2;
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨ξ, h4, h⟩
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
    simp at h; subst h
    replace ih := ih h2
    rcases ξ with ⟨Δ', Γ⟩
    simp at h6;
    replace h4 := pattern_binders_sound h4
    replace h6 := infer_type_sound ih h6
    apply ListGlobalWf.cons
    · apply GlobalWf.inst
      · apply lk
      · rfl
      · simp; apply h4
      · simp; apply h6
    · apply ih
  · cases h

case _ ih => -- odata
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h
  apply ListGlobalWf.cons
  · apply GlobalWf.odata h
  · apply ih h2


theorem lookup_entry_global {G : GlobalEnv}:
  lookup x G = some (Entry.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨τ, (Ts, R)⟩)⟩)⟩) ->
  ∃ i : Nat, G[i]? = some (Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨τ, (Ts, R)⟩)⟩)⟩) := by
intro h
fun_induction lookup <;> simp at *
case _ ctors _ ctors' ih _ =>
  replace h := Vec.fold_or h
  cases h
  case _ h =>
    replace ih := ih h
    rcases ih with ⟨i, ih⟩
    exists i.succ
  case _ h =>
    unfold ctors' at h; simp at h
all_goals try (
  case _ ih _ =>
  replace ih := ih h
  rcases ih with ⟨i, ih⟩
  exists i.succ)
case _ =>
  exists 0; simp; apply h
case _ ih =>
  replace ih := ih h
  rcases ih with ⟨i, ih⟩
  exists i.succ

theorem mk_open_pattern_inversion {g : Global}:
  mk_open_pattern x nc g = some p ->
  ∃ t, g = .inst x p t := by
intro h
unfold mk_open_pattern at h;
cases g <;> simp at *
rcases h with ⟨⟨e1, e2⟩, p⟩
subst e1; subst e2; simp at *; assumption


theorem mk_open_patterns_inversion {G : GlobalEnv} {ps : List _} :
  mk_open_patterns G x nc = ps ->
  ∀ p ∈ ps,
  ∃ g ∈ G, (mk_open_pattern x nc g = some p)
:= by
 intro h1 i h2
 unfold mk_open_patterns at h1
 rw[<-List.mem_filterMap]; subst h1; apply h2;

theorem open_exhaustive_sound {G : GlobalEnv} :
  ⊢ G ->
  G.check_open_exhaustive = some d ->
  OpenExhaustive G
:= by
intro wf h
unfold OpenExhaustive
intro x na nb nc Ks1 Ks2 Ts R q lk qh
unfold GlobalEnv.check_open_exhaustive at h;
simp at h;
replace lk := lookup_entry_global lk
rcases lk with ⟨oi, lk⟩
have temp := List.mem_of_getElem? lk
have h' := h (Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) temp
unfold GlobalEnv.check_insts at h'
simp at h'
rcases h' with ⟨⟨ℓ, ⟨ref_matrix, idxs⟩⟩, h'⟩
have lem := pattern_exhaustive_sound wf qh h'
rcases lem with ⟨i, lem⟩;
generalize zdef : mk_open_patterns G x nc = z at *
generalize z2def : Vec.from_list z = z2 at *
rcases z2 with ⟨ℓ', z2⟩
simp at i;
have e := Vec.from_list_length z2def
simp at e; subst e;
simp at lem; simp at h'; simp at idxs
have lem1 : z2[i] = z[i] := Vec.from_list_indexing2 z2def i
rw[lem1] at lem; clear lem1
have lem3 := mk_open_patterns_inversion zdef z[i] (by simp)
rcases lem3 with ⟨g, g_in_gs, lem3⟩
rw[List.mem_iff_getElem?] at g_in_gs
rcases g_in_gs with ⟨i, g_in_gs⟩
simp [mk_open_pattern] at lem3
split at lem3
case _ j _ _ _ p t =>
  simp at lem3; rcases lem3 with ⟨⟨e1, e2⟩, lem3⟩
  subst e1; subst e2; simp at lem3; subst lem3;
  exists i; exists t; exists z[j]
· cases lem3

end Core
