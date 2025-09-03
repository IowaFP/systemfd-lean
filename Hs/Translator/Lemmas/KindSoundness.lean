import Hs.HsTerm
import Hs.Monad
import SystemFD.Term
import SystemFD.Judgment

import Hs.Translator.Kinds

theorem compile_kind_shape_sound (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Term.IsKind k' := by
intro wf j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; constructor
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  constructor; assumption; assumption

theorem compile_kind_shape_arr (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  k = (κ1 `-k> κ2) ->
  ∃ κ1' κ2', k' = (κ1' -k> κ2') := by
intro wf j1 j2 j3
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j3; case _ j3a j3b =>
cases j3a; cases j3b
case _ ih1 ih2 =>
cases j2; case _ j2 =>
cases j2; case _ j2 =>
cases j2; case _ j2 =>
cases j2; case _ j2 =>
cases j2; case _ k1 h1 k2 h2 =>
cases j1; case _ j1a j1b =>
replace ih1 := ih1 j1a h1
replace ih2 := ih2 j1b h2

sorry




theorem compile_kind_size (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  k.size = k'.size := by
intro wf  j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; simp
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  simp; rw[ih1, ih2]


theorem compile_kind_sound (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Γ ⊢ k' : c := by
intro wf e1 j;
induction c, k using compile_kind.induct generalizing k' <;> simp at *
case _ => cases j; constructor; assumption
case _ k1 k2 ih1 ih2 =>
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases e1;
  case _ e1 e2 =>
  replace ih1 := ih1 e1 h1;
  replace ih2 := ih2 e2 h2;
  constructor; assumption; assumption

theorem compile_star : compile_kind Γ □ `★ = DsM.ok ★ := by simp


theorem dsm_get_type_sound : ⊢ Γ ->
  DsM.toDsM s (Γ d@ h).get_type = .ok τ -> Γ ⊢ #h : τ := by
intro wf j
unfold DsM.toDsM at j
let gt := (Γ d@ h).get_type
generalize fh : Γ d@ h = f at *;
cases f;
all_goals try (
  simp at j;
  unfold Frame.get_type at j; simp at j
)
all_goals try (
  cases j; apply Judgment.var wf;
  unfold Frame.get_type; rw[fh]
)
