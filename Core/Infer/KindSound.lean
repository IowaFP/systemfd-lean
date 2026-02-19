import Core.Infer.Kind
import Core.Ty
import Core.Typing

namespace Core

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
all_goals (try case _ => constructor; assumption)
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h4, h⟩
  simp at h; cases h
  replace ih1 := ih1 h1
  replace ih2 := ih2 h3
  replace h2 := base_kind_some h2
  replace h4 := base_kind_some h4
  cases h2; cases h4
  constructor; assumption; assumption
case _ ih1 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  simp at h; rcases h with ⟨h2, h3⟩
  subst h2; subst h3
  replace ih1 := ih1 h1
  constructor; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  simp at h; cases h.1.1; cases h.1.2; cases h.2; clear h
  have ih1 := ih1 h1
  have ih2 := ih2 h2
  constructor; assumption; assumption
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h3, h⟩
  simp at h; cases h.1; cases h.2; clear h
  replace h3 := is_arrow_some h3; rw[h3] at h1
  have ih1 := ih1 h1
  have ih2 := ih2 h2
  constructor; assumption; assumption

end Core
