import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename

open LeanSubst


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
  case _ h2' _ _ _ _ _ h _ =>
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
  sorry
case ctor1 v _ ih =>
  cases v <;> simp [Term.spine] at h1
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨_, h1, h2⟩; cases h2
  cases r
  all_goals (try simp [Term.spine] at h1)
  case _ h _ =>
    simp [Term.spine] at h; symm at h;
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h, e⟩; cases e
    rw[h1] at h; cases h
    simp [is_stable] at h2; case _ h2' _ _ _ _ _ =>
    cases h2
    case _ w _ _ _ _ _ _ _ _ _ h =>
      have lem := @is_stable_implies_not_is_openm w.fst G (by simp [is_stable]; assumption)
      apply lem h2'
    case _ h3 _ _ h4 _ h =>
      simp [OpenVarVal] at h
      rcases h with ⟨_, h⟩
      replace h :=  h _ h3
      simp at h4; omega
  case _ h => sorry
  sorry
case ctor2 v f _ ih1 ih2 =>
  cases v <;> simp at *
  all_goals (try simp [Term.spine] at h1)
  case _ b =>
    cases b <;> simp at *
    case closed =>
      cases r <;> try simp [Term.spine] at h1
      case _ h _ =>
        simp [Term.spine] at h; symm at h;
        rw[Option.bind_eq_some_iff] at h; rcases h with ⟨w, h, e⟩; cases e
        rcases h1 with ⟨_, e, h1⟩
        rw[h1] at h; cases h
        simp [is_stable] at h2; case _ h2' _ _ _ _ _ =>
        cases h2
        case _ w _ _ _ _ _ _ _ _ _ h =>
          have lem := @is_stable_implies_not_is_openm x G (by simp [is_stable]; assumption)
          apply lem h2'
        case _ h3 _ _ h4 _ h =>
          simp [OpenVarVal] at h
          rcases h with ⟨_, h⟩
          replace h :=  h _ h3
          simp at h4; rw[e] at h; simp at h; omega
      case _ => sorry
      all_goals (try case _ h _ => simp at h)
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
        case _ w _ _ _ _ _ _ _ _ _ h =>
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

theorem instance_type_preservation :
  ⊢ G ->
  G&Δ, Γ ⊢ g#x : T ->
  instances x G = is ->
  ∀ t ∈ is, G&Δ, Γ ⊢ t : T := by
intro wf j h t t_in_is
sorry

theorem preservation_lemma :
  Δ = [] -> Γ = [] ->
  G&Δ, Γ ⊢ t : T ->
  G ⊢ t ~> t' ->
  G&Δ, Γ ⊢ t' : T  := by
intro e1 e2 j h
induction j generalizing t' <;> simp at *
case var h' _ => rw[e2] at h'; simp at h'
all_goals (cases e1; cases e2)
all_goals (try simp at *)
case global => sorry
  -- cases h; simp at *;
  -- case _ h _ _ _ =>
  -- cases h
  -- sorry
case mtch =>
  sorry
case guard =>
  cases h
  case guard_matched => sorry
  case guard_missed => sorry
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  · sorry
  · sorry
  · constructor
    sorry
    sorry
    sorry
    sorry

case app => sorry
case appt => sorry
case lam =>
  cases h;
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
case lamt =>
  cases h;
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
  all_goals (case _ h _ => simp at h)
case cast tj cj _ ih =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case _ => cases cj; assumption
  case _ t _ c _ _ _ t' h cr =>
    simp at *; replace ih := ih cr
    constructor; assumption; assumption
  case _ =>
    cases cj; case _ cj =>
    cases cj; constructor; assumption
  case _ =>
    cases cj; case _ cj _ _ =>
    cases cj;
    apply Typing.choice
    assumption
    constructor; assumption; assumption
    constructor; assumption; assumption

case refl =>
  cases h
  case _ h _ => cases h
  case _ h => simp [Term.spine] at h
case sym =>
  cases h;
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)

  case _ h _ => cases h; constructor; assumption
  case _ ih t' r => replace ih := ih r; constructor; assumption
  case _ j _ =>
    cases j; case _ j =>
    cases j; case _ K _ _ _ _ _ =>
    apply Typing.zero (K := ★)
    constructor; assumption; assumption
  case _ j ih =>
    cases j; case _ j _ _ =>
    cases j
    apply Typing.choice
    constructor; assumption; assumption
    constructor; assumption
    constructor; assumption
case seq =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
case appc => sorry
case arrowc => sorry
case fst => sorry
case snd => sorry
case allc =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp [Term.spine] at h)
  case _ h => cases h; case _ h => constructor; constructor; assumption
  case _ h _ =>
    simp at h
    constructor; simp;
    sorry -- where did my induction hypothesis go?
    sorry
  case _ h =>
    cases h; case _ h =>
    cases h;
    constructor; constructor; sorry; sorry
  case _ h =>
    cases h
    constructor
    constructor;
    sorry;
    sorry
    constructor; simp; assumption
    constructor; simp; assumption

case apptc =>
  cases h
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  all_goals (try case _ h _ _ => simp at h)
  case _ e1 e2 _ _ _ h1 _ h2 _ =>
    cases h1; cases h2
    rw[<-e1] at e2; rw[e2]; rw[e1]
    constructor; case _ j1 _ j2 _ =>
    cases j1; case _ j1 =>
    have lem := Kinding.beta j1 j2
    sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

case zero =>
  cases h;
  case _ h _ => cases h
  all_goals (try case _ h => simp [Term.spine] at h)

case choice =>
  cases h
  all_goals (try assumption)
  all_goals (try case _ h => simp [Term.spine] at h)
  all_goals (try case _ h _ => simp [Term.spine] at h)
  case _ ih _ _ _ r =>
    replace ih := ih r
    apply Typing.choice; assumption; assumption; assumption
  case _ ih _ _ r =>
    replace ih := ih r
    apply Typing.choice; assumption; assumption; assumption
  all_goals (case _ h _ _ => simp at h)


theorem preservation :
  G&[], [] ⊢ t : T ->
  G ⊢ t ~> t' ->
  G&[], [] ⊢ t' : T  := by intro j r; apply preservation_lemma rfl rfl j r
