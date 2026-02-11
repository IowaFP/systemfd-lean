import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename

-- this means that the type of n.apply sp should be and arrow type
theorem refl_spine_lemma :
  OpenVarVal G n sp ->
  ¬ (G&Δ, Γ ⊢ (g#n).apply sp : (A ~[K]~ B)) := by
intro h j
generalize tdef : (g#n).apply sp = t at *
generalize Tdef : (A ~[K]~ B) = T at *
-- induction j <;> simp at *

sorry

theorem refl_is_val :
  G&Δ, Γ ⊢ t : (A ~[K]~ B) ->
  Value G t ->
  ((t = refl! A) ∧ A = B) ∨ (∃ c1 c2, t = c1 `+ c2) := by
intro j h; induction h
any_goals (solve | cases j)
case refl =>
  cases j; constructor; simp
case choice t1 t2 _ _ ih1 ih2 =>
  cases j; apply Or.inr;  exists t1; exists t2
case app ih =>
  sorry


theorem var_val_sound :
  t.spine = some (x, sp) ->
  is_stable x G ∨ OpenVarVal G x sp ->
  ∀ t', ¬ G ⊢ t ~> t' := by
intro h1 h2 t' r
induction t generalizing x sp G
any_goals (simp [Term.spine] at h1)
case global =>
  cases r;
  case inst h2' _ _ _ _ h _ =>
    simp [is_stable] at h2;   simp [Term.spine] at h
    rcases h1 with ⟨e1, e2⟩; cases e1; cases e2; simp at *
    rcases h with ⟨e1, e2⟩; cases e1; cases e2; simp at *
    cases h2
    case _ h =>
      have lem := lookup_entry_openm_exists h2';
      rcases lem with ⟨_, _, lem⟩
      simp [is_ctor, is_instty] at h; rw[lem] at h
      simp at h; simp [Entry.is_ctor, Entry.is_instty] at h
    case _ h3 _ _ _ _ h =>
      simp [OpenVarVal] at h;
      rcases h with ⟨_, h⟩
      replace h := h _ h3; omega
  case defn e _ _ _ h3 h4 =>
    cases h1.1; cases h1.2; clear h1
    simp [Term.spine] at h4; cases h4.1; cases h4.2; clear h4
    replace h3 := lookup_defn_is_defn_sound h3
    cases h2
    case _ h2 =>
      replace h2 := is_stable_implies_not_is_defn h2
      contradiction
    case _ h =>
      simp [OpenVarVal, is_openm] at h;
      rcases h with ⟨h, _⟩
      replace h3 := lookup_entry_defn_exists h3
      rcases h3 with ⟨_, _, _, h3⟩
      rw[h3] at h; simp [Entry.is_openm] at h
case ctor1 v _ ih =>
  cases v <;> simp [Term.spine] at h1
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨_, h1, h2⟩; cases h2
  cases r
  all_goals (try simp [Term.spine] at h1)
  case inst h _ =>
    simp [Term.spine] at h; symm at h;
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h, e⟩; cases e
    rw[h1] at h; cases h
    simp [is_stable] at h2; case _ h2' _ _ _ _ _ =>
    cases h2
    case _ w _ _ _ _ _ _ _ h =>
      have lem := @is_stable_implies_not_is_openm w.fst G (by simp [is_stable]; assumption)
      apply lem h2'
    case _ h3 _ _ h4 _ h =>
      simp [OpenVarVal] at h
      rcases h with ⟨_, h⟩
      replace h :=  h _ h3
      simp at h4; omega
  case defn h _ =>
    sorry

  sorry
case ctor2 v f _ ih1 ih2 =>
  cases v <;> simp at *
  all_goals (try simp [Term.spine] at h1)
  case _ b =>
    cases b <;> simp at *
    case closed =>
      cases r <;> try simp [Term.spine] at h1
      all_goals (try case _ h _ => simp at h)
      case inst h _ =>
        simp [Term.spine] at h; symm at h;
        rw[Option.bind_eq_some_iff] at h; rcases h with ⟨w, h, e⟩; cases e
        rcases h1 with ⟨_, e, h1⟩
        rw[h1] at h; cases h
        simp [is_stable] at h2; case _ h2' _ _ _ _ _ =>
        cases h2
        case _ w _ _ _ _ _ _ _ h =>
          have lem := @is_stable_implies_not_is_openm x G (by simp [is_stable]; assumption)
          apply lem h2'
        case _ h3 _ _ h4 _ h =>
          simp [OpenVarVal] at h
          rcases h with ⟨_, h⟩
          replace h :=  h _ h3
          simp at h4; rw[e] at h; simp at h; omega
      case defn h _ => sorry

      case _ h => sorry -- simp at h
      sorry
    case «open» =>
      cases r <;> try simp [Term.spine] at h1
      case _ h _ =>
        simp [Term.spine] at h; symm at h;
        rw[Option.bind_eq_some_iff] at h; rcases h with ⟨w, h, e⟩; cases e
        rcases h1 with ⟨_, e, h1⟩
        rw[h1] at h; cases h
        simp [is_stable] at h2; case _ h2' _ _ _ _ _ =>
        cases h2
        case _ w _ _ _ _ _ _ _ h =>
          have lem := @is_stable_implies_not_is_openm x G (by simp [is_stable]; assumption)
          apply lem h2'
        case _ h3 _ _ h4 _ h =>
          simp [OpenVarVal] at h
          rcases h with ⟨_, h⟩
          replace h :=  h _ h3
          simp at h4; rw[e] at h; simp at h; omega
      case _ => sorry
      case _ h _ => sorry
      sorry
      sorry
      sorry


theorem value_sound :
  Value G t ->
  t ≠ `0 ∧ ∀ t', ¬ G ⊢ t ~> t' := by
intro h; induction h
case _ =>
  simp at *
  constructor;
  intro h; case _ tnf _ _ _ _  => rw[h] at tnf; simp [Term.spine] at tnf
  case _ tnf _ _ h _ =>
  apply var_val_sound (Eq.symm tnf); assumption
all_goals (
  case _ =>
  apply And.intro; simp
  intro t' r;
  cases r <;> simp at *
  try case right.ctor2_congr1 ih1 ih2 _ r _ =>
      cases ih1; case _ h1 h2 =>
      apply h2 _ r
  try case right.ctor2_congr2 ih1 ih2 _ r _ =>
      cases ih2; case _ h1 h2 =>
      apply h2 _ r
  try case _ h _ _ => simp [Term.spine] at h
  try case _ h => simp [Term.spine] at h
)

theorem reduction_sound :
  G ⊢ t ~> t' -> ¬ Value G t := by
intro r v
have lem := value_sound v
rcases lem with ⟨_ , lem⟩
apply lem t' r
