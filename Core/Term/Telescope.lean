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
  (.ty A tl, b)
| Λ[K] t =>
  let (tl, b) := t.telescope
  (.kind K tl, b)
| t => (.nil, t)

def Term.tele_intro : Term -> Telescope -> Term
| t, .nil => t
| t, .ty A tl => λ[A] (t.tele_intro tl)
| t, .kind K tl => Λ[K] (t.tele_intro tl)

theorem Term.telescope_eq_law {t : Term} :
  t.telescope = (te, b) ->
  b.tele_intro te = t
:= by
  intro j
  induction te generalizing t b
  case nil =>
    simp [Term.tele_intro]
    cases t <;> try simp [Term.telescope, *] at j
    all_goals try rw [j]
    case tbind v _ _ =>
    cases v <;> simp [Term.telescope] at j
    rw [j]
  case kind hd tl ih =>
    simp [Term.tele_intro]
    cases t <;> try simp [Term.telescope] at j
    case tbind v K2 t =>
    cases v <;> simp [Term.telescope] at j
    rcases j with ⟨⟨e1, e2⟩, e3⟩; subst e1 e2 e3
    generalize zdef : t.telescope = z at *
    rcases z with ⟨ztele, z⟩ <;> simp at *
    apply ih zdef
  case ty hd tl ih =>
    simp [Term.tele_intro]
    cases t <;> try  simp [Term.telescope] at j
    case tbind v _ _=> cases v <;> simp [Term.telescope] at j
    case lam C t =>
      rcases j with ⟨⟨e1, e2⟩, e3⟩; subst e1 e2 e3
      generalize zdef : t.telescope = z at *
      rcases z with ⟨ztele, z⟩ <;> simp at *
      apply ih zdef

def Term.telescope_lam_count : Telescope -> Nat
| .nil => 0
| .ty _ tl => telescope_lam_count tl + 1
| .kind _ tl => telescope_lam_count tl

@[simp]
def tele_lift : Telescope -> Subst Term -> Subst Term
| .nil, σ => σ
| .ty _ te, σ => tele_lift te σ.lift
| .kind _ te, σ => tele_lift te (σ ◾ +1@Ty)

@[simp]
def tele_lift_ty : Telescope -> Subst Ty -> Subst Ty
| .nil, σ => σ
| .ty _ te, σ => tele_lift_ty te σ
| .kind _ te, σ => tele_lift_ty te σ.lift

@[simp]
def tele_lift_ren : Telescope -> Ren -> Ren
| .nil, r => r
| .ty _ te, r => tele_lift_ren te r.lift
| .kind _ te, r => tele_lift_ren te r

@[simp]
def tele_lift_iterated : Telescope -> IteratedSubst -> IteratedSubst
| _, .nil => .nil
| te, .term σ it => .term (tele_lift te σ) (tele_lift_iterated te it)
| te, .type σ it => .type (tele_lift_ty te σ) (tele_lift_iterated te it)

@[simp]
theorem telescope_subst {b : Term} :
  (b.tele_intro te)[σ:Term] = b[tele_lift te σ:_].tele_intro te
:= by
  induction te generalizing b σ
  case nil => simp [Term.tele_intro]
  case kind hd te ih =>
    simp [Term.tele_intro]
    replace ih := @ih (σ ◾ +1@Ty) b
    simp at ih; apply ih
  case ty hd te ih =>
    simp [Term.tele_intro]
    replace ih := @ih σ.lift b
    simp at ih
    rw [ih]

@[simp]
theorem telescope_subst_ty {b : Term} :
  (b.tele_intro te)[σ:Ty] = b[tele_lift_ty te σ:_].tele_intro te[σ:_]
:= by
  induction te generalizing b σ
  case nil =>
    simp [Term.tele_intro]
  case kind hd te ih =>
    simp [Term.tele_intro]
    replace ih := @ih σ.lift b
    simp at ih
    rw [ih]
  case ty hd tl ih =>
    simp [Term.tele_intro, *]
