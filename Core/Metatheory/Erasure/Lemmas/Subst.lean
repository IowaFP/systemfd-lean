import Core.Global
import Core.Term
import Core.Typing
import Core.Metatheory.Global
import Core.Reduction
import Core.Untyped
import Core.Metatheory.Erasure.Definition

open Lilac
open LeanSubst
open List

namespace Core

theorem Pattern.erasure_subst (σ : Subst Ty) : (m : Nat) → (pmn : Pattern m) →
  ⟦pmn.smap σ⟧ = pmn.erase
| 0, .nil => by rfl
| n + 1, .cons _ _ => by 
  simp; apply Pattern.erasure_subst

theorem erasure_subst_ty (σ : Subst Ty) : (b : Term) → ⟦b[σ]⟧ = ⟦b⟧
| #x | d#x | .ctor0 _ => by rfl
| .spctor v s v1 v2 ts => by
  simp [Term.erase]; funext;
  apply ((fun b' => erasure_subst_ty σ b') <$> ts)
| .ctor1 (.appt _) b => by simp; apply erasure_subst_ty σ b
| .ctor1 (.prj n) b => by simp; apply erasure_subst_ty σ b
| .ctor2 .app t1 t2 => by
    simp
    apply And.intro <;> try apply erasure_subst_ty
| .ctor2 .apptc _ _ => by rfl
| .cast _ _ t => by simp; apply erasure_subst_ty
| .tbind .allc _ t => by simp; apply erasure_subst_ty
| .tbind .lamt _ t => by simp; apply erasure_subst_ty
| .mtch m n vm pmn vn => by
    simp; apply And.intro; funext;
    apply ((fun b' => erasure_subst_ty σ b') <$> vm)
    apply And.intro; funext;
    apply Pattern.erasure_subst
    funext;
    apply erasure_subst_ty
| .lam _ t => by simp; apply erasure_subst_ty

theorem erasure_subst_ty_su (b : Term) (t : Ty):
  ⟦b[su t::+0σ]⟧ = ⟦b⟧ := by apply erasure_subst_ty

theorem erasure_subst_cons {a : Action Term} {σ : Subst Term} :
  ⟦a :: σ⟧  = ⟦a⟧ :: ⟦σ⟧ := by 
  simp[Subst.cons]
  funext x
  cases x
  trivial
  case _ x => 
    split
    case _ a n heq =>
      rw[show re n = ⟦re n⟧ by simp]
      rw[←heq] 
      simp; trivial
    case _ a t heq => 
      -- TODO: determine why ⟦su t⟧
      -- is ambiguous
      rw[show su ⟦t⟧ = Action.erase (su t) by simp]
      rw[←heq]
      simp; trivial

-- TODO: determine why this isn't 
-- automatically used.
@[simp]
theorem erasure_subst_ren_n {n : Nat} :
  Action.erase (re n) = re n := by trivial

theorem erasure_ren {t : Term} {r : Ren Term} :
  ⟦Term.rmap r t⟧ = Untyped.Term.rmap { act := r.act } ⟦t⟧ := by
    cases t <;> try simp[Term.erase]
    case _ =>
      funext n
      apply erasure_ren
    case _ a t => 
      cases a <;> try simp <;> try apply erasure_ren
    case _ a t1 t2 =>
      cases a <;> try simp <;> try apply erasure_ren
      case app => 
        apply And.intro <;> try apply erasure_ren
    case _ a _ t => 
      cases a <;> try simp <;> try apply erasure_ren
      case lamt => 
        
        cases t <;> try simp <;> cases r <;> try simp[Ren.cons]
        case _ a act => 
          -- TODO: requires showing that act 0 = 0, act (n + 1) = act n + 1
          cases a <;> try simp
          repeat sorry
        repeat sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry

theorem erasure_subst_ren {σ : Subst Term} {r : Ren Term}:
  ⟦σ ∘ r⟧ = ⟦σ⟧ ∘ ⟦r⟧ := by
  simp[Subst.compose_ren_right]
  funext x
  simp[Subst.act, SubstAction.act]
  generalize zdef : σ.inner x = z
  cases z <;> try simp
  case _ t => apply erasure_ren

-- theorem erasure_sub_tm_lam (σ : Subst Term) :
--   ⟦(λ[a]t)[σ]⟧ = ⟦λ[a]t⟧[⟦σ⟧] := by
--   simp [LeanSubst.smap]
--   cases t
--   case _ => sorry
--   repeat sorry

-- set_option pp.notation false
theorem erasure_sub_tm (σ : Subst Term) (b : Term) :
  ⟦b[σ]⟧ = ⟦b⟧[⟦σ⟧] := 
  match b with
  | #_ => by
    simp[LeanSubst.smap, Subst.act, SubstAction.act]
    split
    case _ heq => rw[heq]; trivial
    case _ heq => rw[heq]; trivial
  | d#_ | .ctor0 _ => by rfl 
  | .spctor _ _ _ _ vn => by
    simp[LeanSubst.smap]
    funext n
    apply erasure_sub_tm σ (vn n)
  | .ctor1 (.appt _) t => by 
    simp[LeanSubst.smap]
    apply And.intro
    case _ => apply erasure_sub_tm
    rfl
  | .ctor1 (.prj _) _ => by simp; apply erasure_sub_tm
  | .ctor2 .app t1 t2 => by
    simp[LeanSubst.smap]
    apply And.intro <;> apply erasure_sub_tm
  | .ctor2 .apptc _ _ => by rfl
  | .lam a t => by
      simp[LeanSubst.smap, -Subst.erase]
      rw[←show ⟦Ren.succ Term⟧ = Ren.succ Untyped.Term by trivial] 
      rw[←erasure_subst_ren]
      generalize hs : σ ∘ Ren.succ Term = s
      rw[←show ⟦re 0⟧ = re 0 by simp]
      rw[←erasure_subst_cons (a := re 0)]
      apply erasure_sub_tm
  | .tbind .allc _ t => by
    simp[Subst.hcompose_ren]
    sorry
  | .tbind .lamt _ t => by
    simp[Subst.hcompose_ren]
    sorry
  | .cast _ _ _ => by simp; apply erasure_sub_tm
  | .mtch n m vn pnm vm => by
    simp[LeanSubst.smap]
    apply And.intro
    case _ => 
      funext ⟨i, lt⟩ 
      apply erasure_sub_tm σ (vn ⟨i, lt⟩)
    case _ =>
      funext k
      sorry

theorem erasure_su_cons (t : Term) :
  ⟦su t :: Subst.id Term⟧ = su ⟦t⟧ :: Subst.id Untyped.Term := by
    cases t <;> try simp[Subst.cons] <;> funext n
    case var x =>
      -- TODO: turn into a tactic!
      split
      case _ => grind
      case _ t heq => 
        cases t <;> (try simp) <;> repeat grind
    case defn x =>
      split
      case _ => grind
      case _ t heq =>
        cases t <;> (try simp) <;> repeat grind
    case spctor =>
      repeat split <;> try simp <;> try repeat grind
      case _ heq =>
        split at heq <;> try simp
        case _ => 
          injection heq with heq
          rw[←heq]
          simp
        case _ => contradiction
    case ctor0 a =>
      split; split
      contradiction
      grind
      split
      case _ _ _ heq =>
        simp at heq
        cases a
        rw[←heq]
        simp
      contradiction
    case ctor1 a t =>
      repeat split <;> try simp <;> try repeat grind
    case ctor2 a t =>
      repeat split <;> try simp <;> try repeat grind
    case tbind =>
      repeat split <;> try simp <;> try repeat grind
    case lam =>
      repeat split <;> try simp
      contradiction
      grind
      split
      case _ heq =>
        split at heq
        injection heq with ht
        rw[←ht]
        simp
        contradiction
      contradiction
    repeat sorry

theorem erasure_sub_tm_su (b : Term) :
  ⟦b[su t :: Subst.id Term]⟧
  = ⟦b⟧[su ⟦t⟧ :: Subst.id Untyped.Term] := by 
    rw[erasure_sub_tm (su t :: Subst.id Term) b]
    rw[erasure_su_cons]


