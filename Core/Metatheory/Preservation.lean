import Core.Term
import Core.Term.Spine
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

@[simp]
theorem Vec.to_index {v : Fun.Vec α _} : v.to[i] = v i := sorry

def List.firstM_eq_some : ∀ {ℓ}, List.firstM f ℓ = some t -> ∃ (k : Nat) (h : k < ℓ.length), f ℓ[k] = some t
| .nil, h => by injection h
| .cons hd tl, h => by
  simp at h; rcases h with h | ⟨h1, h2⟩
  exists 0; apply Exists.intro; apply h; simp
  rcases List.firstM_eq_some h2 with ⟨k, q1, q2⟩
  exists (k + 1); apply Exists.intro; apply q2
  simp; exact q1

def PatternBinders.subst {ss S : Vec _ m} :
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
    unfold Constructor.subst at h5; subst w1
    have lem2 := Nat.decLe (Vec.to_list v1).length j
    rcases lem2 with lem2 | lem2
    case _ =>
      replace h6 : (Vec.to_list v1)[j]? = some A := by grind
      cases h1; case _ D1 D2 Ts j1 j2 j3 j4 j5 j6 =>
      sorry
    case _ =>
      replace h6 : (ξ ++ Γ)[j]? = some A := sorry
      replace ih := @ih p1 ξ _ sstl Stl lem1 h2 w2 h4 rfl h6
      sorry

def open_data_subst {ts : Fun.Vec _ _} :
  lookup_spctor_type G ctor = some D1 ->
  KindingPreamble G Δ As D1 D2 ->
  Ty.typescope n D2 = some (Ts, T) ->
  (∀ i, G&Δ,Γ ⊢ ts i : Ts[i]) ->
  Term.IsData .odata ts.to ctors ->
  get_instance ctor i G = some ⟨n, p, b⟩ ->
  Pattern.Match ctors p ->
  Constructor.subst ctors = σ ->
  ∀ j A, ((Vec.to_list Ts) ++ Γ)[j]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γ ⊢ σ j : A
:= by
  sorry


set_option maxHeartbeats 800000
theorem preservation_step (wf : ⊢ G) : G&Δ,Γ ⊢ t : T -> G ⊢ t ~> t' -> G&Δ,Γ ⊢ t' : T
| .global j1 j2, (.defn h) => sorry
| .mtch (ξ := ξ) j1 j2 j3 j4 j5, .data_match (σ := σ) (i := i) h1 h2 h3 =>
  let lem := PatternBinders.subst (cast (by simp) j1) (j3 i) h1 h2 h3
  Typing.subst Γ σ wf lem (j4 i)
| .mtch (S := S) j1 j2 j3 j4 j5, .match_congr (ss' := ss') i h1 h2 =>
  let j1' : ∀ k, G&Δ,Γ ⊢ ss' k : S k := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j1 k) (h1 |> cast (by rw [h]))
    | isFalse h => j1 k |> cast (by rw [h2 k h])
  .mtch j1' j2 j3 j4 j5
| .spctor (Ts := Ts) j1 j2 j3 j4 j5 j6, .openm_match (b := b) (σ := σ) (i := i) h1 h2 h3 h4 =>
  let lem1 : G&Δ,((Vec.to_list Ts) ++ Γ) ⊢ b : T := sorry
  let lem2 := open_data_subst j1 j2 j3 j4 h1 h2 h3 h4
  Typing.subst Γ σ wf lem2 lem1
| .spctor (Ts := Ts) j1 j2 j3 j4 j5 j6, .openm_congr (ts' := ts') i h1 h2 =>
  let j4' : ∀ k, G&Δ,Γ ⊢ ts' k : Ts[k] := λ k =>
    match decEq k i with
    | isTrue h => preservation_step wf (j4 k) (h1 |> cast (by rw [h]))
    | isFalse h => j4 k |> cast (by rw [h2 k h])
  .spctor j1 j2 j3 j4' j5 j6
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
