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

theorem List.firstM_eq_some : ∀ {ℓ}, List.firstM f ℓ = some t -> ∃ (k : Nat) (h : k < ℓ.length), f ℓ[k] = some t
| .nil, h => by injection h
| .cons hd tl, h => by
  simp at h; rcases h with h | ⟨h1, h2⟩
  exists 0; apply Exists.intro; apply h; simp
  rcases List.firstM_eq_some h2 with ⟨k, q1, q2⟩
  exists (k + 1); apply Exists.intro; apply q2
  simp; exact q1

-- theorem open_method_pattern_binders (wf : ⊢ G):
--   lookup_spctor_type G ctor = some D1 ->
--   KindingPreamble G Δ As D1 D2 ->
--   Ty.typescope n D2 = some (Ts, T) ->
--   get_instance ctor i G = some ⟨n, (p, b)⟩ ->
--   Sequ.append (List.map su As) +0 = τ ->
--   ∃ ξ, PatternBinders n Ts p[τ:Ty] ξ
-- := by
--   sorry
theorem List.getElem_swap_index {ℓ : List α} {i j : Nat} (e : i = j) (h1 : i < ℓ.length)
  : ℓ[i] = ℓ[j]
:= by
  sorry

theorem Vec.get_list_to_get {v : Vec α (n + 1)} (h : i < n + 1) : v.list[i]'(by simp [h]) = v[Fin.ofNat (n + 1) i] := sorry

theorem PatternBinders.ctors_type_length {ss S : Vec _ m} :
  --(∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  PatternBinders G Δ m S p ζ ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  ζ.length = (Constructor.subst_type ctors).length
:= by
  sorry

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
    cases h4; case _  c q m1 As1 m2 As2 na2 ts Bs e4 cs e5 j4 =>
    cases h3; case _ m1' m2' n' c'' t' t1 t2 t3 e6 ts' e7 j5 =>
    subst e4; cases e7; case _ =>
    cases e5; case _ =>
    simp [Constructor.subst_type] at h
    simp [Constructor.subst]
    sorry
    -- cases Nat.decLt i nc
    -- case _ nh =>
    --   replace nh : i ≥ nc := by grind
    --   rw [Subst.append_action_ge (h := by simp [nh])]; simp
    --   rw [List.getElem?_append_right (by simp [nh])] at h; simp at h
    --   replace h1 := λ (i:Fin n) => h1 i.succ; simp at h1
    --   apply ih h1 j5 j4 (i - nc) A _ h5
    --   sorry
    -- case _ nh =>
    --   rw [Subst.append_action_lt (h := by simp [nh])]; simp
    --   rw [List.getElem?_append_left (by simp [nh])] at h
    --   rw [List.getElem?_eq_getElem (by simp [nh])] at h; cases h; case _ =>
    --   replace h1 := h1 0; simp at h1; subst e6
    --   cases h1; case _ R'' Ks1' Ks2' Ts' Ts'' q1 q2 q3 q4 q5 q6 q7 q8 =>
    --   rw [j1] at q2; cases q2; case _ =>
    --   simp; cases nc; cases nh; case _ nc =>
    --   simp; have lem : nc - i < nc + 1 := by grind
    --   rw [Vec.get_list_to_get lem, Vec.get_list_to_get lem]
    --   sorry

-- theorem PatternBinders.ctors_type_length_lemma {ss S : Vec _ m} :
--   --(∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
--   PatternBinders G Δ m S p ζ ξ ->
--   Term.IsData v ss ctors ->
--   Pattern.Match ctors p ->
--   Ren.add Ty ζ.length ∘ (Constructor.subst_type ctors ++ Subst.id Ty) = +0σ
-- := by
--   intro h1 h2 h3
--   have lem := ctors_type_length h1 h2 h3
--   rw [lem]
--   rw [Subst.rewrite4_append_add_direct (ℓ := Constructor.subst_type ctors)]
--   sorry
-- theorem PatternBinders.subst {ss S : Vec _ m} :
--   (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
--   PatternBinders G Δ m S p ξ ->
--   Term.IsData v ss ctors ->
--   Pattern.Match ctors p ->
--   Constructor.subst ctors = σ ->
--   ∀ j A, (ξ ++ Γ)[j]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γ ⊢ σ j : A
-- := by
--   intro h1 h2 h3 h4 h5 j A h6 h7
--   induction ctors generalizing ξ σ
--   case _ =>
--     simp at *; cases h2; simp at h6
--     unfold Constructor.subst at h5; subst h5; simp
--     apply Typing.var h6 h7
--   case _ n c v ih =>
--     rcases c with ⟨c, As, ts⟩
--     cases ss; case _ sshd sstl =>
--     cases S; case _ Shd Stl =>
--     have lem1 := λ (i : Fin n) => h1 i.succ; simp at lem1
--     replace h1 := h1 0; simp at h1
--     cases h2; case _ v1 v2 q1 q2 q3 q4 q5 q6 q7 =>
--     cases h3; case _ x t2 w1 w2 =>
--     cases h4; case _ Bs n1 ξ e1 e2 h4 =>
--     unfold Constructor.subst at h5;
--     have lem2 := Nat.decLe v1.length j
--     rcases lem2 with lem2 | lem2
--     case _ =>
--       replace h6 : (Vec.to_list v2)[j]? = some A := by sorry
--       sorry
--     case _ =>
--       replace h6 : (v1 ++ Γ)[j]? = some A := sorry
--       replace ih := @ih q5 v1 _ sstl Stl lem1 q7 w2 h4 rfl h6
--       rw [<-h5]
--       sorry

set_option maxHeartbeats 800000
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
| .spctor (n := n) (ts := ts) (Ts := Ts) j1 j2 j3 j4 j5 j6 j7 j8,
  .openm_match (p := p) (b := b) h1 h2 h3 h4 =>
    sorry
  -- let Ts' : Vec Ty n := Vec.map (·[τ]) Ts
  -- let j4' : ∀ (i : Fin n), G&Δ,Γ ⊢ ts.to[i] : Ts'[i] := j4 |> cast (by subst Ts'; simp)
  -- let ⟨ξ, lem2⟩ : ∃ ξ, PatternBinders G Δ n Ts' p[τ:Ty] ξ := sorry
  -- let lem1 : G&Δ,(ξ ++ Γ) ⊢ b[τ:Ty] : T := sorry
  -- let lem3 := PatternBinders.subst j4' lem2 h1 sorry h5
  -- Typing.subst Γ σ wf lem3 (cast (by grind) lem1)
| .spctor (Ts' := Ts') j1 j2 j3 j4 j5 j6 j7 j8, .openm_congr (ts' := ts') i h1 h2 =>
  let j6' : ∀ k, G&Δ,Γ ⊢ ts' k : Ts'[k] := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j6 k) (h1 |> cast (by rw [h]))
    | isFalse h => j6 k |> cast (by rw [h2 k h])
  .spctor j1 j2 j3 j4 j5 j6' j7 j8
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
