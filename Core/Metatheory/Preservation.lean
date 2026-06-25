import Core.Term
import Core.Vec
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Rename
import Core.Metatheory.Substitution
-- import Core.Metatheory.GlobalWf
-- import Core.Metatheory.Uniqueness
-- import Core.Metatheory.Inversion
-- import Core.Metatheory.SpineType
-- import Core.Metatheory.Preservation.Lemmas

open Lilac
open LeanSubst

namespace Core

theorem List.getElem_swap_index {ℓ : List α} {i j : Nat} (e : i = j) (h1 : i < ℓ.length)
  : ℓ[i] = ℓ[j]
:= by
  induction ℓ generalizing i j <;> simp [*]

@[simp]
theorem Vec.get_Fin_ofNat_succ {xs : Vec α (n + 1)} (h : i + 1 < n + 2) : (x :: xs)[Fin.ofNat (n + 2) (i + 1)] = xs[Fin.ofNat (n + 1) i] := by
  unfold Fin.ofNat
  have lem1 : (i + 1) % (n + 2) = i + 1 := by rw [Nat.mod_eq_of_lt h]
  have lem2 : i % (n + 1) = i := by rw [Nat.mod_eq_of_lt]; grind
  simp [lem1, lem2]
  simp [getElem, Vec.get]

theorem Vec.get_list_to_get : {n:Nat} -> {v : Vec α (n + 1)} -> (h : i < n + 1) -> v.list[i]'(by simp [h]) = v[Fin.ofNat (n + 1) i]
| n, .cons x xs, h =>
  match i with
  | 0 => by simp
  | i + 1 =>
    match n with
    | 0 => by simp at h
    | n + 1 =>
      have lem1 : i < n + 1 := by grind
      have lem2 := get_list_to_get (v := xs) lem1
      by rw [Vec.get_Fin_ofNat_succ h]; simp [lem2]

theorem PatternBinders.ctors_type_length {ss S : Vec _ m} :
  PatternBinders G Δ m S p ζ ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  ζ.length = (Constructor.subst_type ctors).length
:= by
  intro h1 h2 h3
  induction h1
  case _ =>
    cases ss; cases h2
    simp [Constructor.subst_type]
  case _ nc c' na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' j1 j2 e1 e2 e3 j3 ih =>
    cases h3; case _  c q m1 As1 m2 As2 na2 ts Bs e4 cs e5 j4 =>
    cases h2; case _ m1' m2' n' c'' t' t1 t2 t3 e6 ts' e7 j5 =>
    subst e4; cases e7; case _ =>
    cases e5; case _ =>
    simp [Constructor.subst_type]
    rw [ih j5 j4]

theorem PatternBinders.ctors_term_length {ss S : Vec _ m} :
  PatternBinders G Δ m S p ζ ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  ξ.length = (Constructor.subst ctors).length
:= by
  intro h1 h2 h3
  induction h1
  case _ =>
    cases ss; cases h2
    simp [Constructor.subst]
  case _ nc c' na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' j1 j2 e1 e2 e3 j3 ih =>
    cases h3; case _  c q m1 As1 m2 As2 na2 ts Bs e4 cs e5 j4 =>
    cases h2; case _ m1' m2' n' c'' t' t1 t2 t3 e6 ts' e7 j5 =>
    subst e4; cases e7; case _ =>
    cases e5; case _ =>
    simp [Constructor.subst]
    subst e2; simp; rw [ih j5 j4]

theorem PatternBinders.ctors_type {ss S : Vec _ m} :
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  PatternBinders G Δ m S p ζ ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  ∀ (i: Nat) K, (ζ ++ Δ)[i]? = some K → G&Δ ⊢ ((Constructor.subst_type ctors ++ Subst.id Ty).act i) : K
:= by
  intro h1 h2 h3 h4
  induction h2
  case _ ss _ =>
    cases ss; cases h3; cases h4; simp
    intro i K h2
    apply Kinding.var h2
  case _ nc c' na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' j1 j2 e1 e2 e3 j3 ih =>
    intro i K h
    cases h4; case _  c q m1 As1 m2 As2 na2 ts Bs e4 cs e5 j4 =>
    cases h3; case _ m1' m2' n' c'' t' t1 t2 t3 e6 ts' e7 j5 =>
    subst e4; cases e7; case _ =>
    cases e5; case _ =>
    have lem1 := PatternBinders.ctors_type_length j3 j5 j4
    simp [Constructor.subst_type]
    cases Nat.decLt i (ℓ1.length + nb)
    case _ nh =>
      replace nh : i ≥ ℓ1.length + nb := by grind
      rw [Subst.append_action_ge (by simp; rw [<-lem1]; simp [nh])]; simp; rw [<-lem1]
      rw [List.getElem?_append_right (by simp [nh])] at h; simp at h
      rw [List.getElem?_eq_getElem (by grind)] at h
      generalize zdef : Δ[i - (ℓ1.length + nb)]'(by grind) = z at *
      cases h; case _ =>
      rw [<-zdef]; apply Kinding.var; simp
    case _ nh =>
      rw [Subst.append_action_lt (by simp; rw [<-lem1]; simp [nh])]
      rw [List.getElem?_append_left (by simp [nh])] at h
      cases Nat.decLt i ℓ1.length
      case _ nh2 =>
        replace nh2 : i ≥ ℓ1.length := by grind
        rw [List.getElem_append_right (by grind)]
        rw [List.getElem?_append_right (by grind)] at h
        rw [List.getElem?_eq_getElem (by grind)] at h
        generalize zdef : Ks2.list.reverse[i - ℓ1.length]'(by grind) = z at *
        cases h; case _ =>
        rw [List.getElem_swap_index (i := i - (Constructor.subst_type cs).length) (j := i - ℓ1.length) (by simp [lem1])]
        rw [<-zdef]; simp
        replace h1 := h1 0; simp at h1; subst e6
        cases h1; case _ R'' Ks1' Ks2' Ts' Ts'' q1 q2 q3 q4 q5 q6 q7 q8 =>
        rw [j1] at q2; cases q2; case _ =>
        cases nb; cases Ks2; simp at h; case _ nb =>
        simp; have lem : nb - (i - ℓ1.length) < nb + 1 := by grind
        rw [Vec.get_list_to_get lem, Vec.get_list_to_get lem]
        apply q5
      case _ nh2 =>
        rw [List.getElem_append_left (by grind)]
        rw [List.getElem?_append_left (by grind)] at h
        replace h1 := λ (i:Fin n) => h1 i.succ; simp at h1
        replace ih := ih h1 j5 j4 i K (by grind)
        rw [Subst.append_action_lt (by rw [<-lem1]; simp [nh2])] at ih
        apply ih

theorem PatternBinders.ctors_term {ss S : Vec _ m} :
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  PatternBinders G Δ m S p ζ ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  ∀ (i:Nat) A, (ξ[Constructor.subst_type ctors ++ Subst.id Ty] ++ Γ)[i]? = some A ->
    G&Δ ⊢ A : ★ ->
    G&Δ,Γ ⊢ ((Constructor.subst ctors ++ Subst.id Term).act i) : A
:= by
  intro h1 h2 h3 h4
  induction h2
  case _ ss _ =>
    cases ss; cases h3; cases h4
    simp [Constructor.subst_type]
    intro i K h2 h3
    simp [Constructor.subst]
    apply Typing.var h2 h3
  case _ nc c' na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' j1 j2 e1 e2 e3 j3 ih =>
    intro i A h h5
    cases h4; case _ c q m1 As1 m2 As2 na2 ts Bs e4 cs e5 j4 =>
    cases h3; case _ m1' m2' n' c'' t' t1 t2 t3 e6 ts' e7 j5 =>
    subst e4; cases e7; case _ =>
    cases e5; case _ =>
    have lem1 := PatternBinders.ctors_term_length j3 j5 j4
    have lem2 := PatternBinders.ctors_type_length j3 j5 j4
    simp [Constructor.subst_type] at h
    rw [e1, e2] at h
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k] at h
    rw [Subst.subst_append_assoc] at h
    rw [Subst.compose_ren_left_cons_lift_indirect (h := lem2)] at h
    rw [Subst.rewrite4_append_add_indirect (h := by simp)] at h
    rw [Subst.compose_ren_right_assoc] at h
    rw [Subst.rewrite4_append_add_indirect (h := lem2)] at h
    generalize σdef : Constructor.subst_type cs ++ Subst.id Ty = σ at h
    generalize τdef :
      ((List.map su As.list).reverse ++ Subst.id Ty).lift nb
        ∘ ((List.map su As2.list).reverse ++ Subst.id Ty) = τ at h
    simp [Constructor.subst]
    cases Nat.decLt i (ℓ2.length + nc)
    case _ nh =>
      replace nh : i ≥ ℓ2.length + nc := by grind
      rw [Subst.append_action_ge (by simp; rw [<-lem1]; simp [nh])]; simp; rw [<-lem1]
      rw [<-List.append_assoc] at h
      rw [List.getElem?_append_right (by simp; grind)] at h; simp at h
      rw [List.getElem?_eq_getElem (by grind)] at h
      simp at h; rw [<-h]
      apply Typing.var; simp
      rw [h]; apply h5
    case _ nh =>
      rw [Subst.append_action_lt (by simp; rw [<-lem1]; simp [nh])]
      rw [<-List.append_assoc] at h
      rw [List.getElem?_append_left (by simp; grind)] at h
      cases Nat.decLt i ℓ2.length
      case _ nh2 =>
        replace nh2 : i ≥ ℓ2.length := by grind
        rw [List.getElem_append_right (by grind)]
        rw [List.getElem?_append_right (by simp; grind)] at h
        rw [List.getElem?_eq_getElem (by grind)] at h
        have hh := h
        simp at h; rw [<-h]; simp
        have h1' := h1 0; simp at h1'; subst e6
        cases h1'; case _ R'' Ks1' Ks2' Ts' Ts'' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
        rw [j1] at q3; cases q3; case _ =>
        cases nc
        case _ => cases Ts; simp at hh; grind
        case _ nc nch =>
          simp
          rw [Vec.get_list_to_get (by grind), Vec.get_to]
          rw [Vec.get_list_to_get (by grind)]
          rw [<-lem1]
          rw [Subst.compose_left_cons_lift_indirect (h := by simp)] at τdef
          simp at τdef; subst q7; simp at q8; rw [<-τdef]
          subst e1 q9; clear h1
          simp at e3
          rw [<-Subst.subst_append_assoc]
          have lem : As1 = As := by
            rw [Subst.subst_append_assoc] at e3
            have leme1 : (List.map su As2⟨Ren.add Ty nb⟩.list).reverse = List.map su (As2⟨Ren.add Ty nb⟩.list).reverse := by simp
            have leme2 : (List.map su As1⟨Ren.add Ty nb⟩.list).reverse = List.map su (As1⟨Ren.add Ty nb⟩.list).reverse := by simp
            have leme3 : (List.map su As⟨Ren.add Ty nb⟩.list).reverse = List.map su (As⟨Ren.add Ty nb⟩.list).reverse := by simp
            rw [leme1, leme2, leme3] at e3
            replace e3 := FV.subst_congr_append_append (by simp; apply q1 _ rfl) (by simp) (by simp) e3
            simp at e3
            have leme4 : As1⟨Ren.add Ty nb⟩⟨Ren.sub Ty nb⟩ = As⟨Ren.add Ty nb⟩⟨Ren.sub Ty nb⟩ := by rw [e3]
            simp at leme4; apply leme4
          subst lem; apply q8
      case _ nh2 =>
        rw [List.getElem_append_left (by grind)]
        rw [List.getElem?_append_left (by simp; apply nh2)] at h
        replace h1 := λ (i:Fin n) => h1 i.succ; simp at h1
        replace ih := ih h1 j5 j4 i A (by grind) h5
        rw [Subst.append_action_lt (by rw [<-lem1]; simp [nh2])] at ih
        apply ih

theorem preservation_open_data_match_lemma {As : Vec Ty m1} {Bs : Vec Ty m2} {ts : Fun.Vec Term n} {i : Nat} (wf : ⊢ G) :
  lookup_spine_type G x = some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ ->
  Ts' = Ts[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  R' = R[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  (∀ (i:Fin m1), G&Δ ⊢ As[i] : Ks1[i]) ->
  (∀ (i:Fin m2), G&Δ ⊢ Bs[i] : Ks2[i]) ->
  (∀ (i:Fin n), G&Δ,Γ ⊢ ts i : Ts'[i]) ->
  (∀ (i:Fin n), Ty.data? DataConst.opn G Ts[i]) ->
  Term.IsData .opn ts.to ctors ->
  G[i]? = some (Global.inst x p b) ->
  Pattern.Match ctors p ->
  (t' = b[Constructor.subst_type ctors ++ Subst.id Ty][Bs.list.reverse.map su ++ As.list.reverse.map su ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term]) ->
  G&Δ,Γ ⊢ t' : R'
:= by
  intro j1 e1 e2 j2 j3 j4 j5 j6 j7 j8 e3
  have lem1 := GlobalWf.index_instance wf j7
  cases lem1; case _ m1' Ks1' m2' Ks2' R'' Δ' ζ Γ' e4 Ts2 q1 q2 q3 =>
  unfold lookup_spine_type at j1
  generalize zdef : lookup x G = z at *
  cases z; simp at q1; case _ z =>
  cases q1; case _ =>
  simp [Entry.spine_type] at j1
  rcases j1 with ⟨e, j1⟩; subst e; simp at j1
  rcases j1 with ⟨e, e', j1⟩; subst e e'; simp at j1
  rcases j1 with ⟨e, e', e''⟩; subst e e' e'' e1 e2 e3 e4
  have lem1 := PatternBinders.ctors_type_length q2 j6 j8
  --have lem2 := PatternBinders.ctors_type sorry q2 j6 j8
  replace q3 := Typing.subst_type (Ks1'.list ++ Ks2'.list).reverse (Constructor.subst_type ctors ++ Subst.id Ty) wf sorry q3
  simp at q3; rw [Subst.rewrite4_append_add_indirect (h := lem1)] at q3; simp at q3
  replace q3 := Typing.subst_type [] (List.map su Bs.list.reverse ++ List.map su As.list.reverse ++ Subst.id Ty) wf sorry q3
  replace q3 := Typing.subst [] (Constructor.subst ctors ++ Subst.id Term) wf sorry q3
  replace q3 := q3.extend Δ Γ
  simp at q3; simp; exact q3

set_option maxHeartbeats 800000 in
theorem preservation_step (wf : ⊢ G) : G&Δ,Γ ⊢ t : T -> G ⊢ t ~> t' -> G&Δ,Γ ⊢ t' : T
| .defn j1 j2, .defn (A := A) j3 =>
  have e : T = A := by rw [j1] at j3; grind
  match EntryWf.from_lookup_defn wf j3 with
  | .defn q1 q2 q3 => q2.extend Δ Γ ▸ simp [e]
| .mtch (ξ := ξ) (ts := ts) j1 j2 j3 j4 j5, .data_match (ctors := ctors) (i := i) h1 h2 h3 =>
  have lem1 := PatternBinders.ctors_type (Γ := Γ) (cast (by grind) j1) (j3 i) h1 h2
  have lem2 := PatternBinders.ctors_term (Γ := Γ) (cast (by grind) j1) (j3 i) h1 h2
  have lem3 := PatternBinders.ctors_type_length (j3 i) h1 h2
  have j4 : G&Δ,((ξ i)[Constructor.subst_type ctors ++ Subst.id Ty] ++ Γ) ⊢ (ts i)[Constructor.subst_type ctors ++ Subst.id Ty] : T :=
    Typing.subst_type Δ (Constructor.subst_type ctors ++ Subst.id Ty) wf lem1 (j4 i) ▸ simp [lem3]
  have j4 := Typing.subst Γ (Constructor.subst ctors ++ Subst.id Term) wf lem2 j4
  j4 ▸ rw [h3]
| .mtch (S := S) j1 j2 j3 j4 j5, .match_congr (ss' := ss') i h1 h2 =>
  let j1' : ∀ k, G&Δ,Γ ⊢ ss' k : S k := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j1 k) (h1 |> cast (by rw [h]))
    | isFalse h => j1 k |> cast (by rw [h2 k h])
  .mtch j1' j2 j3 j4 j5
| .spctor j1 j2 j3 j4 j5 j6 j7 j8 j9, .openm_match h1 h2 h3 h4 =>
    preservation_open_data_match_lemma wf j1 j2 j3 j4 j5 j6 (j9 rfl) h1 h2 h3 h4
| .spctor (Ts' := Ts') j1 j2 j3 j4 j5 j6 j7 j8 j9, .openm_congr (ts' := ts') i h1 h2 =>
  let j6' : ∀ k, G&Δ,Γ ⊢ ts' k : Ts'[k] := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j6 k) (h1 |> cast (by rw [h]))
    | isFalse h => j6 k |> cast (by rw [h2 k h])
  .spctor j1 j2 j3 j4 j5 j6' j7 j8 j9
| .app (.lam j2 j4) j3, .beta => Typing.beta wf j4 j3
| .app j1 j2, .app_congr r =>
  let j1' := preservation_step wf j1 r
  .app j1' j2
| .appt (.lamt j1 j3) j2 e, .betat =>
  Typing.beta_type wf j3 j2 |> cast (by simp; rw [e])
| .appt j1 j2 e, .ctor1_congr r =>
  let j1' := preservation_step wf j1 r
  .appt j1' j2 e
| .cast j1 (.refl j2) j3 e, .cast => j3 |> cast (by rw [e])
| .cast j1 j2 j3 e, .cast_congr r =>
  let j2' := preservation_step wf j2 r
  .cast j1 j2' j3 e
| .prj (.refl $ .app j1 j2) (.fst_app j3), .prj_fst_app => .refl j3
| .prj (.refl $ .app j1 j2) (.snd_app j3), .prj_snd_app => .refl j3
| .prj (.refl $ .arrow j1 j2) (.fst_arrow j3), .prj_fst_arr => .refl j3
| .prj (.refl $ .arrow j1 j2) (.snd_arrow j3), .prj_snd_arr => .refl j3
| .prj j1 j2, (.ctor1_congr r) =>
  let j1' := preservation_step wf j1 r
  .prj j1' j2
| .allc (.refl j), .allc => .refl (.all j)
| .allc j, .allc_congr r =>
  let j' := preservation_step wf j r
  .allc j'
| .apptc (.refl (.all j1)) (.refl j2) e1 e2, .apptc =>
  Typing.refl (Γ := Γ) (.beta j1 j2) |> cast (by rw [e1, e2])
| .apptc j1 j2 e1 e2, .apptc_congr1 r =>
  let j1' := preservation_step wf j1 r
  .apptc j1' j2 e1 e2
| .apptc j1 j2 e1 e2, .apptc_congr2 r =>
  let j2' := preservation_step wf j2 r
  .apptc j1 j2' e1 e2
| _, _ => sorry
