import Core.Term
import Core.Vec
import Core.Reduction
import Core.Typing
import Core.Util

import Core.Metatheory.Rename
import Core.Metatheory.Substitution

open Lilac
open LeanSubst

namespace Core

theorem Pattern.Match.subst_type (σ : Subst Ty)
  : Pattern.Match c p -> Pattern.Match c p[σ]
| .nil => .nil
| .cons (Bs := Bs) j e1 e2 =>
  have lem := Pattern.Match.subst_type σ j
  .cons (Bs := Bs[σ]) lem e1 (by rw [e2])

theorem List.getElem_swap_index {ℓ : List α} {i j : Nat} (e : i = j) (h1 : i < ℓ.length)
  : ℓ[i] = ℓ[j]
:= by
  induction ℓ generalizing i j <;> simp [*]

theorem PatternBinders.ctors_type_length {ss S : Vec _ m} :
  PatternBinders v1 G Δ m S p ζ ξ ->
  Term.IsData v2 ss ctors ->
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
  PatternBinders v1 G Δ m S p ζ ξ ->
  Term.IsData v2 ss ctors ->
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
  PatternBinders v G Δ m S p ζ ξ ->
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
        cases h1; case _ R'' Ks1' Ks2' Ts' Ts'' q1 q2 q3 q4 q5 q6 q7 q8 q9 =>
        rw [j1] at q4; cases q4; case _ =>
        cases nb; cases Ks2; simp at h; case _ nb =>
        simp; have lem : nb - (i - ℓ1.length) < nb + 1 := by grind
        rw [Vec.get_list_to_get lem, Vec.get_list_to_get lem]
        apply q6
      case _ nh2 =>
        rw [List.getElem_append_left (by grind)]
        rw [List.getElem?_append_left (by grind)] at h
        replace h1 := λ (i:Fin n) => h1 i.succ; simp at h1
        replace ih := ih h1 j5 j4 i K (by grind)
        rw [Subst.append_action_lt (by rw [<-lem1]; simp [nh2])] at ih
        apply ih

theorem PatternBinders.ctors_term {ss S : Vec _ m} :
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  PatternBinders v G Δ m S p ζ ξ ->
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
        rw [j1] at q4; cases q4; case _ =>
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
  lookup_spine_type .openm G x = some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ ->
  Ts' = Ts[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  R' = R[(As.list ++ Bs.list).reverse.map su ++ Subst.id Ty] ->
  (∀ (i:Fin m1), G&Δ ⊢ As[i] : Ks1[i]) ->
  (∀ (i:Fin m2), G&Δ ⊢ Bs[i] : Ks2[i]) ->
  (∀ (i:Fin n), G&Δ,Γ ⊢ ts i : Ts'[i]) ->
  (∀ (i:Fin n), Ty.data? DataConst.opn G Ts[i]) ->
  Term.IsData .opn ts.to ctors ->
  G[i]? = some (Global.inst x p b) ->
  Pattern.Match ctors p ->
  (t' = b[Constructor.subst_type ctors ++ Bs.list.reverse.map su ++ As.list.reverse.map su ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term]) ->
  G&Δ,Γ ⊢ t' : R'
:= by
  intro j1 e1 e2 j2 j3 j4 j5 j6 j7 j8 e3
  have lem1 := GlobalWf.index_instance wf j7
  cases lem1; case _ m1' Ks1' m2' Ks2' R'' Δ' ζ ξ e4 Ts2 q1 q2 q3 =>
  unfold lookup_spine_type at j1
  generalize zdef : lookup x G = z at *
  cases z; simp at q1; case _ z =>
  cases q1; case _ =>
  simp [Entry.spine_type] at j1
  rcases j1 with ⟨e, j1⟩; subst e; simp at j1
  rcases j1 with ⟨e, e', j1⟩; subst e e'; simp at j1
  rcases j1 with ⟨e, e', e''⟩; subst e e' e'' e1 e2 e3 e4
  have lem_len := PatternBinders.ctors_type_length q2 j6 j8
  have lem0 := PatternBinders.extend Δ q2; clear q2
  replace lem0 := PatternBinders.subst_type Δ (List.map su (As.list ++ Bs.list).reverse ++ Subst.id Ty) wf (by {
    intro i K h; simp at h
    cases Nat.decLt i (m1' + m2')
    case _ h2 =>
      replace h2 : i ≥ m1' + m2' := by omega
      rw [<-List.append_assoc] at h
      rw [List.getElem?_append_right (by simp; omega)] at h; simp at h
      rw [Subst.append_action_ge (by simp; omega)]; simp
      apply Kinding.var h
    case _ h2 =>
      rw [<-List.append_assoc] at h
      rw [List.getElem?_append_left (by simp; omega)] at h
      rw [Subst.append_action_lt (by simp; omega)]; simp
      cases Nat.decLt i m2'
      case _ h3 =>
        replace h3 : i ≥ m2' := by omega
        rw [List.getElem?_append_right (by simp; omega)] at h; simp at h
        rw [List.getElem_append_right (by simp; omega)]; simp
        rw [List.getElem?_reverse (by simp; omega)] at h; simp at h
        rw [List.getElem?_eq_getElem (by simp; omega)] at h; cases h
        cases m1'; grind; case _ m1' =>
        simp; rw [Vec.get_list_to_get (by omega), Vec.get_list_to_get (by omega)]
        generalize jdef : Fin.ofNat (m1' + 1) (m1' - (i - m2')) = j
        apply j2 j
      case _ h3 =>
        rw [List.getElem?_append_left (by simp; omega)] at h
        rw [List.getElem_append_left (by simp; omega)]; simp
        rw [List.getElem?_reverse (by simp; omega)] at h; simp at h
        rw [List.getElem?_eq_getElem (by simp; omega)] at h; cases h
        cases m2'; cases h3; case _ m2' =>
        simp; rw [Vec.get_list_to_get (by omega), Vec.get_list_to_get (by omega)]
        generalize jdef : Fin.ofNat (m2' + 1) (m2' - i) = j
        apply j3 j
  }) lem0
  have jb := q3.extend Δ Γ⟨Ren.add Ty ζ.length⟩⟨(Ren.add Ty (m1' + m2')).lift ζ.length⟩
  replace jb := Typing.subst_type (ζ ++ Δ) ((List.map su Bs.list.reverse ++ List.map su As.list.reverse ++ Subst.id Ty).lift ζ.length) wf (by {
    intro i K h1
    rw [List.append_assoc] at h1
    cases Nat.decLt i ζ.length
    case _ h2 =>
      replace h2 : i ≥ ζ.length := by omega
      rw [List.getElem?_append_right (by omega)] at h1
      rw [Subst.lift_action_ge (by omega)]
      cases Nat.decLt (i - ζ.length) (m1' + m2')
      case _ h3 =>
        have h4 : i - ζ.length ≥ m1' + m2' := by omega
        rw [List.getElem?_append_right (by simp; omega)] at h1
        rw [Subst.append_action_ge (by simp; omega)]; simp
        apply Kinding.var; simp at h1
        rw [List.getElem?_append_right (by omega)]; simp; exact h1
      case _ h3 =>
        rw [List.getElem?_append_left (by simp; omega)] at h1
        rw [Subst.append_action_lt (by simp; omega)]; simp; simp at h1
        cases Nat.decLt (i - ζ.length) m2'
        case _ h4 =>
          replace h4 : i - ζ.length ≥ m2' := by omega
          rw [List.getElem?_append_right (by simp; omega)] at h1
          rw [List.getElem_append_right (by simp; omega)]
          rw [List.getElem?_reverse (by simp; omega)] at h1
          rw [List.getElem?_eq_getElem (by simp; omega)] at h1; cases h1; simp
          cases m1'; grind; case _ m1' =>
          simp; rw [Vec.get_list_to_get (by omega), Vec.get_list_to_get (by omega)]
          generalize jdef : Fin.ofNat (m1' + 1) (m1' - (i - ζ.length - m2')) = j
          have lem := j2 j
          apply Kinding.rename (ζ ++ Δ) (Ren.add Ty ζ.length) _ lem
          intro i; simp
          rw [List.getElem?_append_right (by omega)]; simp
        case _ h4 =>
          rw [List.getElem?_append_left (by simp; omega)] at h1
          rw [List.getElem_append_left (by simp; omega)]; simp
          rw [List.getElem?_reverse (by simp; omega)] at h1
          rw [List.getElem?_eq_getElem (by simp; omega)] at h1; cases h1; simp
          cases m2'; cases h4; case _ m2' =>
          simp; rw [Vec.get_list_to_get (by omega), Vec.get_list_to_get (by omega)]
          generalize jdef : Fin.ofNat (m2' + 1) (m2' - (i - ζ.length)) = j
          have lem := j3 j
          apply Kinding.rename (ζ ++ Δ) (Ren.add Ty ζ.length) _ lem
          intro i; simp
          rw [List.getElem?_append_right (by omega)]; simp
    case _ h2 =>
      rw [List.getElem?_append_left (by omega)] at h1
      rw [Subst.lift_action_lt (by omega)]
      apply Kinding.var; grind
  }) jb
  have q3' : ∀ (i : Fin n), G&Δ,Γ ⊢ (ts.to)[i] : Ts2[List.map su (As.list ++ Bs.list).reverse ++ Subst.id Ty][i] := by
    intro i; rw [Vec.get_to]; apply j4 i
  have j8' := Pattern.Match.subst_type (List.map su (As.list ++ Bs.list).reverse ++ Subst.id Ty) j8
  have lem1 := PatternBinders.ctors_type (Γ := Γ) q3' lem0 j6 j8'
  replace jb := Typing.subst_type Δ (Constructor.subst_type ctors ++ Subst.id Ty) wf lem1 jb
  have lem2 := PatternBinders.ctors_term (Γ := Γ) q3' lem0 j6 j8'
  have e1 : List.map su Bs.list.reverse ++ List.map su As.list.reverse = List.map su (As.list ++ Bs.list).reverse := by simp
  have e2 : ∀ {A : List Ty}, A⟨(Ren.add Ty (m1' + m2')).lift ζ.length⟩[(List.map su (As.list ++ Bs.list).reverse ++ Subst.id Ty).lift ζ.length] = A := by
    intro A; simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren]
    rw [<-Subst.rewrite_lift_compose_ren_left]
    rw [Subst.rewrite4_append_add_indirect]; simp; simp; omega
  have e3 : ∀ {A : List Ty}, A⟨Ren.add Ty ζ.length⟩[Constructor.subst_type ctors ++ Subst.id Ty] = A := by simp [lem_len]
  rw [Subst.List.smap_append, Subst.List.smap_append, e1, e2, e3] at jb
  replace jb := Typing.subst Γ (Constructor.subst ctors ++ Subst.id Term) wf lem2 jb
  simp; simp [-Subst.rewrite_lift_k] at jb
  rw [<-Subst.compose_commute_add_ren_subst] at jb; simp [-Subst.rewrite_lift_k, lem_len] at jb
  rw [Subst.compose_lift_append_indirect rfl] at jb
  apply jb

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
| .prj (.refl $ .app j1 j2) (.fst_app j3 j4), .prj_fst_app => .refl j3
| .prj (.refl $ .app j1 j2) (.snd_app j3 j4), .prj_snd_app => .refl j3
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

#print axioms preservation_step
