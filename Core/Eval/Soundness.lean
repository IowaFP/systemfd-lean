import LeanSubst
import Core.Reduction
import Core.Reduction.Definition
import Core.Eval.SmallStep

open Lilac

namespace Core

theorem Term.is_data_sound :
  Term.is_data dc s = some c ->
  Term.IsData dc s c
:= by
  intro h
  fun_induction Term.is_data <;> simp at *
  case _ =>
    subst h; apply Term.IsData.nil
  case _ ih =>
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
    simp at h; rcases h with ⟨h3, h4⟩
    subst c; subst dc
    replace ih := ih h2
    apply Term.IsData.cons
    apply ih
    simp; apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · apply And.intro
        · rfl
        · apply And.intro
          · rfl
          · apply And.intro
            · rfl
            · apply And.intro
              · rfl
              · rfl
    rfl


theorem get_instance_sound {G : List Global} :
   get_instance x cs G = some ⟨i, _, p, t⟩ ->
   G[i]? = some (Global.inst x p t)
:= by
intro h
induction G <;> (unfold get_instance at h; unfold get_instance_aux at h; simp at *)
sorry

theorem pattern_match_sound {m : Nat} {cs : Vec Constructor m} {ps : Pattern m} :
  pattern_match cs ps = true ->
  Core.Pattern.Match cs ps
:= by

sorry

theorem eval_sound (Γ : GlobalEnv) :
  M.eval Γ = some N ->
  Γ ⊢ M ~> N := by
intro h
fun_induction Term.eval <;> simp at h
case _ =>  -- lookup defn
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  cases h;
  apply Red.defn h2
case _ ih => -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨i, m, p, t⟩, h4, h⟩
  simp at h; rcases h with ⟨⟨e1, h5⟩, h⟩
  subst e1;
  replace h2 := Term.is_data_sound h2
  replace h4 := get_instance_sound h4
  replace h5 := pattern_match_sound (cs := h1) (ps := p) h5
  apply Red.openm_match (i := i) (b := t) (b' := N)
  · apply h2
  · apply h4
  · apply h5
  · simp; symm at h; apply h

case _ => -- openm
  sorry

case _ => -- mtch
  sorry

case _ => -- mtch
  sorry

case _ => -- Λ[K] t •[T]
  sorry

case _ => -- t •[T]
  sorry

case _ => -- λ t • t
  sorry

case _ => -- t • t
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry

case _ =>
  sorry
case _ =>
  sorry

case _ =>
  sorry
case _ =>
  sorry

case _ =>
  sorry
case _ =>
  sorry


end Core
