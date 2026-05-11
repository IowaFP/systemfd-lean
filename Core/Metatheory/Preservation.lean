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

theorem PatternBinders.subst {ss S : Vec _ m} :
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  PatternBinders m S p ξ ->
  Term.IsData v ss ctors ->
  Pattern.Match ctors p ->
  Constructor.subst ctors = σ ->
  ∀ j A, (ξ ++ Γ)[j]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γ ⊢ σ j : A
:= by
  intro h1 h2 h3 h4 h5 j A h6 h7
  induction ctors generalizing ξ σ
  case _ =>
    simp at *; cases h2; simp at h6
    unfold Constructor.subst at h5; subst h5; simp
    apply Typing.var h6 h7
  case _ n c v ih =>
    rcases c with ⟨c, As, ts⟩
    cases ss; case _ sshd sstl =>
    cases S; case _ Shd Stl =>
    have lem1 := λ (i : Fin n) => h1 i.succ; simp at lem1
    replace h1 := h1 0; simp at h1
    cases h2; case _ q1 q2 v1 p1 q5 h2 =>
    cases h3; case _ x t2 w1 w2 =>
    cases h4; case _ Bs n1 ξ h4 =>
    sorry
    -- unfold Constructor.subst at h5; subst w1
    -- have lem2 := Nat.decLe (Vec.to_list v1).length j
    -- rcases lem2 with lem2 | lem2
    -- case _ =>
    --   replace h6 : (Vec.to_list v1)[j]? = some A := by grind
    --   cases h1; case _ D1 D2 Ts j1 j2 j3 j4 j5 j6 =>
    --   sorry
    -- case _ =>
    --   replace h6 : (ξ ++ Γ)[j]? = some A := sorry
    --   replace ih := @ih p1 ξ _ sstl Stl lem1 h2 w2 h4 rfl h6
    --   sorry

set_option maxHeartbeats 800000
theorem preservation_step (wf : ⊢ G) : G&Δ,Γ ⊢ t : T -> G ⊢ t ~> t' -> G&Δ,Γ ⊢ t' : T
| .defn j1 j2, r => sorry
| .mtch (ξ := ξ) j1 j2 j3 j4 j5, .data_match (σ := σ) (i := i) h1 h2 h3 =>
  let lem := PatternBinders.subst (cast (by simp) j1) (j3 i) h1 h2 h3
  Typing.subst Γ σ wf lem (j4 i)
| .mtch (S := S) j1 j2 j3 j4 j5, .match_congr (ss' := ss') i h1 h2 =>
  let j1' : ∀ k, G&Δ,Γ ⊢ ss' k : S k := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j1 k) (h1 |> cast (by rw [h]))
    | isFalse h => j1 k |> cast (by rw [h2 k h])
  .mtch j1' j2 j3 j4 j5
| .spctor (n := n) (ts := ts) (τ := τ) (Ts := Ts) j1 j2 j3 j4 j5 j6 j7,
  .openm_match (p := p) (b := b) (σ := σ) h1 h2 h3 h4 h5 =>
  let Ts' : Vec Ty n := Vec.map (·[τ]) Ts
  let j4' : ∀ (i : Fin n), G&Δ,Γ ⊢ ts.to[i] : Ts'[i] := j4 |> cast (by subst Ts'; simp)
  let ⟨ξ, lem2⟩ : ∃ ξ, PatternBinders n Ts' p[τ:Ty] ξ := sorry
  let lem1 : G&Δ,(ξ ++ Γ) ⊢ b[τ:Ty] : T := sorry
  let lem3 := PatternBinders.subst j4' lem2 h1 sorry h5
  Typing.subst Γ σ wf lem3 (cast (by grind) lem1)
| .spctor (Ts := Ts) (τ := τ) j1 j2 j3 j4 j5 j6 j7, .openm_congr (ts' := ts') i h1 h2 =>
  let j4' : ∀ k, G&Δ,Γ ⊢ ts' k : Ts[k][τ] := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j4 k) (h1 |> cast (by rw [h]))
    | isFalse h => j4 k |> cast (by rw [h2 k h])
  .spctor j1 j2 j3 j4' j5 j6 j7
| .app (.lam j2 j4) j3, .beta => Typing.beta wf j4 j3
| .app j1 j2, .app_congr r =>
  let j1' := preservation_step wf j1 r
  .app j1' j2
| .appt (.lamt j1 j3) j2 e, .betat =>
  Typing.beta_type wf j3 j2 |> cast (by simp; rw [e]; unfold Function.comp; simp)
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
