import Core.Infer.Kind
import Core.Ty
import Core.Typing

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

theorem is_arrow_some {k : Kind} :
  k.is_arrow = some b ->
  k = b.1 -:> b.2 := by
intro h
induction k <;> simp at *
all_goals (unfold Kind.is_arrow at h; simp at h)
rw[<-h]; simp


theorem infer_kind_sound :
  τ.infer_kind G Δ = some k -> ⊢ G -> Kinding G Δ τ k := by
intro h wf
induction Δ, τ using Ty.infer_kind.induct generalizing k <;> simp at *
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
  simp at h; cases h
  replace ih1 := ih1 h1
  replace ih2 := ih2 h4
  replace h3 := base_kind_some h3
  replace h5 := base_kind_some h5
  cases h3; cases h5
  constructor; assumption; assumption
case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace ih1 := ih1 h2
  constructor; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  simp at h; cases h.1.1; cases h.1.2; cases h.2; clear h
  have ih1 := ih1 h2
  have ih2 := ih2 h3
  constructor; assumption; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h5, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace h5 := is_arrow_some h5; rw[h5] at h1
  have ih1 := ih1 h1
  have ih2 := ih2 h3
  constructor; assumption; assumption
