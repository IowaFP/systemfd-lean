import LeanSubst
import Core.Term
import Core.Reduction.Definition
import Core.Reduction.Congr

open LeanSubst

namespace Core

@[grind .]
theorem Value.not_zero : ¬ Value G `0 := by
  intro j; cases j
  case _ x sp j1 j2 j3 =>
  simp [Term.spine] at j3

@[grind .]
theorem Value.spine_sound :
  t.spine = some (x, sp) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> ∀ t', ¬ (G ⊢ t ~> t')) ->
  is_stable G x ∨ OpenVarVal G x sp ->
  ∀ t', ¬ (G ⊢ t ~> t')
:= by
  intro h1 h2 h3 h4 t' r
  induction sp using List.reverse_ind generalizing x t t'
  case nil =>
    replace h1 := Spine.apply_eq h1; simp [Term.apply] at h1; subst h1
    cases h4
    case _ h => cases r <;> grind
    case _ h =>
      obtain ⟨e1, e2⟩ := h
      cases r <;> grind
  case rcons hd tl ih =>
    have lem1 := Spine.apply_eq h1; simp at lem1; subst lem1
    cases hd
    case type =>
      rw [<-Spine.apply_type] at r
      generalize zdef : (g#x).apply tl = z at r
      cases r
      all_goals try solve |
        rw [<-Spine.apply_type, zdef] at h1;
        simp [Term.spine] at h1
      case _ q1 q2 =>
        subst zdef; simp [Term.spine] at q1
        obtain ⟨e1, e2⟩ := q1; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case _ h =>
        subst zdef; simp [Term.spine] at h
        obtain ⟨e1, e2⟩ := h; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case _ t' r =>
        replace ih := @ih x ((g#x).apply tl) (by simp) (by grind) (by grind)
        rw [<-zdef] at r
        apply ih _ t' r
        cases h4; simp [*]
        case _ h4 =>
        apply Or.inr; unfold OpenVarVal at *
        grind
    case oterm =>
      rw [<-Spine.apply_oterm] at r
      generalize zdef : (g#x).apply tl = z at r
      cases r
      case defn q1 q2 =>
        subst zdef; simp [Term.spine] at q2
        obtain ⟨e1, e2⟩ := q2; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case inst h _ =>
        subst zdef; simp [Term.spine] at h
        obtain ⟨e1, e2⟩ := h; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case ctor2_congr1 t' _ r =>
        replace ih := @ih x ((g#x).apply tl) (by simp) (by grind) (by grind)
        rw [<-zdef] at r
        apply ih _ t' r
        cases h4; simp [*]
        case _ h4 =>
        apply Or.inr; unfold OpenVarVal at *
        grind
      case ctor2_congr2 w t2' _ r =>
        apply h3 (.oterm w) (by simp) w rfl _ r
      case ctor2_map2 c1 c2 _ _ =>
        have lem := h2 (.oterm (c1 `+ c2)) (by simp) _ rfl
        simp [Term.spine] at lem
      case ctor2_absorb2 =>
        have lem := h2 (.oterm `0) (by simp) _ rfl
        simp [Term.spine] at lem
      all_goals solve |
        rw [<-Spine.apply_oterm, zdef] at h1
        simp [Term.spine] at h1
    case term =>
      rw [<-Spine.apply_term] at r
      generalize zdef : (g#x).apply tl = z at r
      cases r
      case defn q1 q2 =>
        subst zdef; simp [Term.spine] at q2
        obtain ⟨e1, e2⟩ := q2; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case inst h _ =>
        subst zdef; simp [Term.spine] at h
        obtain ⟨e1, e2⟩ := h; subst e1 e2
        unfold OpenVarVal at h4
        cases h4 <;> grind
      case ctor2_congr1 t' _ r =>
        replace ih := @ih x ((g#x).apply tl) (by simp) (by grind) (by grind)
        rw [<-zdef] at r
        apply ih _ t' r
        cases h4; simp [*]
        case _ h3 =>
        apply Or.inr; unfold OpenVarVal at *
        grind
      all_goals try solve | simp [Ctor2Variant.congr2] at *
      all_goals solve |
        rw [<-Spine.apply_term, zdef] at h1
        simp [Term.spine] at h1

theorem Value.sound : Value G t -> ∀ t', ¬ (G ⊢ t ~> t') := by
  intro j; induction j <;> intro t' r
  case app x sp t j1 j2 j3 j4 ih =>
    cases t
    all_goals try simp [Term.spine] at j1
    case global y =>
      obtain ⟨e1, e2⟩ := j1; subst e1 e2
      cases j4
      case _ h => cases r <;> grind
      case _ h =>
        obtain ⟨q1, q2⟩ := h
        cases r <;> grind
    case ctor1 c t =>
      cases c <;> simp [Term.spine] at j1
      case appt =>
        obtain ⟨a, q1, q2⟩ := Option.bind_eq_some_iff.1 j1; clear j1
        obtain ⟨z, sp'⟩ := a; simp at q2
        obtain ⟨e1, e2⟩ := q2; subst e1 e2
        grind
    case ctor2 c t1 t2 =>
      cases c <;> try simp [Term.spine] at j1
      case app b =>
        cases b <;> simp [Term.spine] at j1
        all_goals
          obtain ⟨a, q1, q2⟩ := Option.bind_eq_some_iff.1 j1; clear j1
          obtain ⟨z, sp'⟩ := a; simp at q2
          obtain ⟨e1, e2⟩ := q2; subst e1 e2
          grind
  case choice => cases r <;> grind
  all_goals
    cases r <;> simp [Term.spine] at *

end Core
