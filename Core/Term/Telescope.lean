import LeanSubst
import Core.Util
import Core.Ty
import Core.Term.Definition
import Core.Term.Substitution
import Core.Term.BEq

open LeanSubst

def Term.telescope : Term -> Telescope × Term
| lam A t =>
  let (tl, b) := t.telescope
  (.ty A :: tl, b)
| Λ[K] t =>
  let (tl, b) := t.telescope
  (.kind K :: tl, b)
| t => ([], t)

def Term.tele_intro : Term -> Telescope -> Term
| t, [] => t
| t, .cons (.ty A) tl => λ[A] (t.tele_intro tl)
| t, .cons (.kind K) tl => Λ[K] (t.tele_intro tl)

theorem Term.telescope_eq_law {t : Term} :
  t.telescope = (tele, b) ->
  b.tele_intro tele = t
:= by
  intro j
  induction tele generalizing t b
  case nil =>
    simp [Term.tele_intro]
    cases t <;> try simp [Term.telescope, *] at j
    all_goals try rw [j]
    case tbind v _ _ =>
    cases v <;> simp [Term.telescope] at j
    rw [j]
  case cons hd tl ih =>
    sorry
    -- cases hd
    -- case kind K =>
    --   simp [Term.tele_intro]
    --   cases t <;> try simp [Term.telescope] at j
    --   case tbind v K2 t =>
    --   cases v <;> simp [Term.telescope] at j
    --   rcases j with ⟨⟨e1, e2⟩, e3⟩; subst e1 e2 e3
    --   generalize zdef : t.telescope = z at *
    --   rcases z with ⟨ztele, z⟩ <;> simp at *
    --   apply ih zdef
    -- case ty A =>
    --   simp [Term.tele_intro]
    --   cases t <;> try  simp [Term.telescope] at j
    --   case tbind v _ _=> cases v <;> simp [Term.telescope] at j
    --   case lam C t =>
    --     rcases j with ⟨⟨e1, e2⟩, e3⟩; subst e1 e2 e3
    --     generalize zdef : t.telescope = z at *
    --     rcases z with ⟨ztele, z⟩ <;> simp at *
    --     apply ih zdef

def Term.telescope_lam_count : Telescope -> Nat
| [] => 0
| .cons (.ty _) tl => telescope_lam_count tl + 1
| .cons (.kind _) tl => telescope_lam_count tl

@[simp]
def tele_lift : Telescope -> Subst Term -> Subst Term
| [], σ => σ
| .cons (.ty _) te, σ => Subst.lift (tele_lift te σ)
| .cons (.kind _) te, σ => (tele_lift te σ) ◾ +1@Ty

@[simp]
def tele_lift_ren : Telescope -> Ren -> Ren
| [], r => r
| .cons (.ty _) te, r => Ren.lift (tele_lift_ren te r)
| .cons (.kind _) te, r => tele_lift_ren te r

@[simp]
theorem tele_lift_re : tele_lift te (re i :: σ) = re i :: tele_lift te σ := by
  sorry

@[simp]
theorem tele_lift_succ : tele_lift te +1 = +1 := by sorry

@[simp]
theorem tele_lift_compose {σ τ : Subst Term}
  : tele_lift te (σ ∘ τ) = tele_lift te σ ∘ tele_lift te τ
:= by
  sorry

@[simp]
theorem tele_lift_hcompose {σ : Subst Term} {τ : Subst Ty}
  : tele_lift te (σ ◾ τ) = tele_lift te σ ◾ τ
:= by
  sorry

@[simp]
theorem telescope_subst {b : Term} :
  (b.tele_intro te)[σ] = b[tele_lift te σ].tele_intro te
:= by
  induction te generalizing b σ
  case nil => simp [Term.tele_intro]
  case cons hd te ih =>
    cases hd
    case kind K =>
      simp [Term.tele_intro]
      replace ih := @ih (σ ◾ +1@Ty) b
      simp at ih; apply ih
    case ty A =>
      simp [Term.tele_intro]
      replace ih := @ih σ.lift b
      simp at ih; apply ih

-- theorem telescope_subst_ty {b : Term} :
--   (b.tele_intro te)[σ:Ty] = b[tele_lift_ty te σ:Ty].tele_intro te
-- := by
--   induction te generalizing b σ
--   case nil => simp [Term.tele_intro]
--   case cons hd tl ih =>
--     cases hd
--     case kind K =>
--       sorry
--     case ty A =>
--       simp [Term.tele_intro]
--       sorry

@[simp]
def tele_lift_ty : Telescope -> Subst Ty -> Subst Ty
| [], σ => σ
| .cons (.ty _) te, σ => tele_lift_ty te σ
| .cons (.kind _) te, σ => Subst.lift (tele_lift_ty te σ)

@[simp]
def tele_lift_iterated : Telescope -> IteratedSubst -> IteratedSubst
| _, .nil => .nil
| te, .term σ it => .term (tele_lift te σ) (tele_lift_iterated te it)
| te, .type σ it => .type (tele_lift_ty te σ) (tele_lift_iterated te it)
