import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Metatheory.Determined.Definition
import Core.Metatheory.GlobalWf

open LeanSubst

namespace Core

theorem determined_progress :
  ⊢ G ->
  G&[],[] ⊢ t : A ->
  t.Determined ->
  Global.Determined G ->
  Value G t ∨ (∃ t', Plus (Red G) t t' ∧ t'.Determined)
:= by
  intro wf j h1 h2
  generalize Δdef : [] = Δ at j
  generalize Γdef : [] = Γ at j
  induction j
  case var j1 j2 => subst Γdef; simp at j1
  case global x A Δ b Γ j1 j2 =>
    cases q1 : is_stable G x
    case _ =>
      have lem := not_stable_implies_openm_or_defn q1
      rw [j1] at lem; simp at lem
      cases lem
      case _ q2 =>
        apply Or.inr
        obtain ⟨T, t, lem⟩ := Global.get_defn q2
        replace h2 := (h2 x).2 T t lem
        exists t; apply And.intro _ h2
        apply Plus.start
        have lem2 := @Red.defn G g#x x [] t (by simp [Term.spine])
        simp at lem2; apply lem2
        simp [lookup_defn]; rw [lem]; simp
      case _ q2 =>
        cases h : A.arity
        case zero =>
          obtain ⟨T, lem1⟩ := Global.get_openm q2
          have lem2 := j1
          simp [lookup_type] at j1; rw [lem1] at j1; simp [Entry.type] at j1
          subst j1
          apply Or.inr
          replace h2 := (h2 x).1 Δ Γ T T [] lem1
          simp [Term.apply] at h2
          apply h2; apply Typing.global lem2 j2; apply h
        case succ a =>
          apply Or.inl; apply Value.app (x := x) (sp := [])
          all_goals try simp [Term.spine]
          apply Or.inr; simp [OpenVarVal]
          apply And.intro q2; intro T q3
          rw [j1] at q3; injection q3 with e; subst e
          omega
    case _ =>
      apply Or.inl; apply Value.app (x := x) (sp := [])
      all_goals try simp [Term.spine]
      apply Or.inl q1
  case mtch => sorry
  case guard => sorry
  case lam => sorry
  case app Δ A b Γ f B a j1 j2 j3 ih1 ih2 =>
    obtain ⟨df, da⟩ := Term.Determined.app.2 h1
    replace ih1 := ih1 df Δdef Γdef
    sorry
  case lamt => sorry
  case appt => sorry
  case cast => sorry
  case refl => sorry
  case sym => sorry
  case seq => sorry
  case appc => sorry
  case arrowc => sorry
  case fst => sorry
  case snd => sorry
  case allc => sorry
  case apptc => sorry
  case zero => sorry
  case choice => sorry

end Core
