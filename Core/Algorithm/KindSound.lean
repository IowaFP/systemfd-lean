import Core.Algorithm.Kind
import Core.Ty
import Core.Typing

theorem wf_kind_sound :
  wf_kind K == .some u -> Sorting K □ := by
intro h
induction K using wf_kind.induct
all_goals (unfold wf_kind at h; simp at h)
constructor
constructor
case _ ih1 ih2 =>
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨u1, h1, h⟩
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨u2, h2, h⟩
cases h; cases u1; cases u2; cases u
constructor
replace h1 := beq_of_eq h1; apply ih1 h1
replace h2 := beq_of_eq h2; apply ih2 h2

theorem base_kind_some {k : Kind}:
  k.base_kind = some b ->
  k = .base b := by
intro h
induction k <;> simp at *
case _ a =>
  cases a
  · unfold Kind.base_kind at h; simp at *; assumption
  · unfold Kind.base_kind at h; simp at *; assumption
case _ => unfold Kind.base_kind at h; simp at h


theorem infer_kind_sound :
  infer_kind G Δ τ = some k -> ⊢ G -> Kinding G Δ τ k := by
intro h wf
induction Δ, τ using infer_kind.induct generalizing k <;> simp at *
all_goals( try
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, _ , h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h, e3⟩
  cases e3; constructor; assumption)
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h6, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace ih1 := ih1 h1
  replace ih2 := ih2 h4
  replace h3 := base_kind_some h3
  replace h5 := base_kind_some h5
  cases h3; cases h5
  constructor; assumption; assumption
sorry
sorry
sorry
