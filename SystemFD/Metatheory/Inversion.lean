import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

theorem inversion_apply_spine :
  Γ ⊢ t.apply_spine sp : A ->
  ∃ B, Γ ⊢ t : B
:= by
intro j; induction sp generalizing Γ t A <;> simp at *
case _ => exists A
case _ hd tl ih =>
  cases hd; case _ v a =>
  cases v <;> simp at *
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 j3 =>
    apply Exists.intro _; apply j1
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j1 j2 j3 =>
    apply Exists.intro _; apply j1
  case _ =>
    replace ih := ih j
    cases ih; case _ B ih =>
    cases ih; case _ j =>
    apply Exists.intro _; apply j

theorem apply_spine_uniform :
  Γ ⊢ a : A ->
  Γ ⊢ b : A ->
  Γ ⊢ a.apply_spine sp : B ->
  Γ ⊢ b.apply_spine sp : B
:= by sorry

theorem ctx_get_term_well_typed :
  ⊢ Γ ->
  Γ d@ x = .term T t ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by sorry

theorem ctx_get_instance_well_typed :
  ⊢ Γ ->
  Γ d@ x = .openm T ->
  ixs = instance_indices' Γ 0 x [] ->
  t ∈ get_instances Γ ixs ->
  Γ ⊢ #x : T ∧ Γ ⊢ t : T
:= by sorry
