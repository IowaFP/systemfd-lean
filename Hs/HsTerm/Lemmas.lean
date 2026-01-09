import Hs.HsTerm.Definition
import Hs.HsTerm.Substitution

namespace HsTerm

theorem application_spine_size (τ : HsTerm) :
  τ.neutral_form = .some nf ->
  ∀ τ' : HsTerm, (nf.2.map (·.2)).elem τ' ->
  τ'.size < τ.size := by
  intro h1 τ' h2
  simp_all; cases h2; case _ h2 =>
  induction τ generalizing nf τ';
  all_goals try (cases h1)
  all_goals try (simp at h2)
  case _ v _ _ ih1 ih2 =>
    cases v <;> simp at h1
    all_goals(
      rw[Option.bind_eq_some_iff] at h1; cases h1;
      case _ sp' nf =>
      cases nf; case _ anf nf =>
      cases nf; simp at h2;
      cases h2;
      case _ h2 =>
        replace ih1 := ih1 anf τ' h2
        simp; omega;
      case _ h2 =>
        cases h2; case _ r l =>
        replace ih1 := ih1 anf τ'
        cases l; cases r; simp; omega;
  )

theorem application_spine_head_size (t : HsTerm) :
  t.neutral_form = .some (h, sp) ->
  h.size ≤ t.size := by
intro h
induction t generalizing sp <;> simp at *
case _ => cases h; case _ h _ => cases h; simp
case _ => cases h; case _ h _ => cases h; simp
case _ cv _ _ ih1 ih2 =>
  cases cv <;>  simp at h
  all_goals (
    rw[Option.bind_eq_some_iff] at h; cases h; case _ h =>
    cases h; case _ w h1 h2 =>
    cases h2;
    have ih1' := @ih1 w.snd h1;
    omega)

end HsTerm
