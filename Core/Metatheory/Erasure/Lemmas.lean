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
    apply And.intro
    apply erasure_subst_ty
    apply erasure_subst_ty
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

-- set_option pp.notation false
theorem erasure_sub_tm (σ : Subst Term) (b : Term) :
  ⟦b[σ]⟧ = ⟦b⟧[⟦σ⟧] := 
  match b with
  | #x => by
    simp[LeanSubst.smap]
    simp[Subst.act, SubstAction.act]
    split
    case _ heq => rw[heq]; trivial
    case _ heq => rw[heq]; trivial
  | .ctor0 _ => by rfl
  | .ctor1 (.prj _) _ => by sorry 
  | .cast _ _ t => by simp; apply erasure_sub_tm
  | _ => sorry

theorem erasure_su (t : Term) :
  ⟦su t :: Subst.id Term⟧ = su ⟦t⟧ :: Subst.id Untyped.Term := by sorry

theorem erasure_sub_tm_su (b : Term) :
  ⟦b[su t :: Subst.id Term]⟧
  = ⟦b⟧[su ⟦t⟧ :: Subst.id Untyped.Term] := by 
    rw[erasure_sub_tm (su t :: Subst.id Term) b]
    rw[erasure_su]

theorem GlobalEnv.lookup_singleton_defn_some :
  lookup x [.defn x a t] = some (.defn x a t) := by simp[lookup]

theorem GlobalEnv.lookup_singleton_some_eq :
  lookup x1 [.defn y a1 t1] = some (.defn x2 a2 t2)
  → x1 = y ∧ x1 = x2 ∧ a1 = a2 ∧ t1 = t2 := by
  unfold lookup
  intros h
  split at h
  grind
  contradiction

theorem GlobalEnv.lookup_inst_none :
  lookup x [.inst s pm t] = none := by simp[lookup]

theorem GlobalEnv.lookup_ctors_vec (vn : Vec (Option Entry) n) :
 Vec.foldr Option.or none vn =
  some (Entry.data y K ctors) := by sorry

theorem GlobalEnv.lookup_data :
  lookup x [.data n y K ctors] = some (.data y K ctors) := by 
  simp[lookup]
  intros hnxy
  sorry
  -- generalize hvn : (Vec.map (fun x_1 => if x = x_1.1.fst then some (Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none)
  --       ctors.zipIdx) = vn
  --
  -- apply GlobalEnv.lookup_ctors_vec vn

theorem GlobalEnv.lookup_singleton_elim :
  lookup x [g] = some (.defn y a t)
  → x = y
  := by
  intros h
  cases g
  case _ n y K ctors => 
    have h2 := @GlobalEnv.lookup_data x n y K ctors
    rw[h2] at h
    grind
  -- TODO: how to remove the case where list is empty?
  case _ => 
    unfold lookup at h
    split at h <;> try (first | simp at h | contradiction)
  case _ => 
    unfold lookup at h
    split at h <;> try (first | simp at h | contradiction)
  case _ => 
    have _ := GlobalEnv.lookup_singleton_some_eq h
    grind
  case _ =>  
    rw[GlobalEnv.lookup_inst_none] at h
    contradiction
  case _ => 
    unfold lookup at h
    split at h <;> try (first | simp at h | contradiction)

theorem GlobalEnv.lookup_from_some :
  lookup x [g] = some (.defn x a t)
  → g = .defn x a t := by 
  intros h
  unfold lookup at h
  split at h <;> try simp
  case h_1 => trivial
  case h_2 n y _ _ _ _ => 
    simp at h
    split at h
    injection h
    contradiction
    rename_i heq hxy
    injection heq with head_eq tail_eq
    unfold Vec.foldr at h
    split at h
    case _ => 
      rw[←tail_eq] at h
      contradiction
    case _ => 
      subst tail_eq
      dsimp[lookup] at h
      sorry
  case h_3 heq => 
    split at h
    injection h; contradiction
    injection heq with head_eq tail_eq
    rw[←tail_eq] at h
    contradiction
  case h_4 heq =>
    injection heq with _ tail_eq
    split at h
    simp at h
    rw[←tail_eq] at h
    contradiction
  case h_5 heq =>
    sorry
  case h_6 heq => 
    injection heq with _ tail_eq
    rw[←tail_eq] at h
    contradiction
  case h_7 heq => 
    split at h
    simp at h
    injection heq with _ tail_eq
    rw[←tail_eq] at h
    contradiction

theorem GlobalEnv.lookup_nomatch :
  lookup x [.defn y a t] = none → x ≠ y := by 
  intros h hxy
  subst hxy
  have h2 := @GlobalEnv.lookup_singleton_defn_some x a t
  rw[h2] at h
  contradiction

theorem lookup_erasure_singleton_some :
 lookup x [g] = some (.defn y a t)
  → Untyped.lookup x [⟦g⟧] = some (.defn y ⟦t⟧)
  := by
    intros h
    simp
    split
    case h_1 => 
      simp
      let ⟨hx1y, hx12, ha12, ht12⟩ := GlobalEnv.lookup_singleton_some_eq h
      apply And.intro
      exact hx1y
      apply And.intro
      rw[←hx1y, hx12]
      rw[ht12]
    case h_2 =>
      simp
      rw[GlobalEnv.lookup_inst_none] at h
      contradiction
    case h_3 g' hp1 hp2 =>
      simp
      rw[GlobalEnv.lookup_singleton_elim h] at h
      have h2 := GlobalEnv.lookup_from_some h
      exact hp1 y a t h2

theorem lookup_erasure_singleton_none :
 lookup x [g] = none
  → Untyped.lookup x [⟦g⟧] = none
  := by
    intros h
    dsimp
    split
    simp[Untyped.lookup]
    case h_1 => exact GlobalEnv.lookup_nomatch h
    case h_2 => simp
    case h_3 => simp

theorem wf_weaken (wf : ⊢ (h :: ts)) : ⊢ ts := by 
  cases wf
  case cons wf _ => apply wf

theorem lookup_erasure (wf : ⊢ G) :
  lookup x G = some (Entry.defn y a t)
  → Untyped.lookup x (map Global.erase G)
    = some (Untyped.Entry.defn x ⟦t⟧) := by
  intro h1
  rcases G with _ | ⟨h, ts⟩
  contradiction
  rw[← List.singleton_append]
  rw[← List.singleton_append] at h1
  have h2 := (Core.lookup_append_some wf h1)
  rcases h2
  case _ heq => 
    rw [List.singleton_append, List.map_cons]
    have heq' := lookup_erasure_singleton_some heq
    rw[←(Untyped.lookup_singleton_elim heq')] at heq'
    apply Untyped.lookup_append_weaken_right heq'
  case _ h3 => 
    let ⟨h3l, h3r⟩ := h3; clear h3
    rw [List.singleton_append, List.map_cons]
    rw [←List.singleton_append]
    let G := map Global.erase ts
    rw[Untyped.lookup_elim_left G (lookup_erasure_singleton_none h3l)]
    rw[←lookup_erasure (wf_weaken wf) h3r]

-- TODO: avoid cases by matching on *G*,
-- JUST the List, not the globals
theorem GlobalEnv.erasure_ty (wf : ⊢ G) :
  lookup_defn G x = some (A, t)
  → Untyped.lookup_defn ⟦G⟧ x = ⟦t⟧ := by
  intro h
  simp[lookup_defn] at h
  simp[Option.bind_eq_some_iff] at h
  rcases h with ⟨e, h1, h2⟩
  cases e <;> (
    rename_i a t;
    try rename_i y;
    try simp at h2
  )
  rcases h2 with ⟨e1, e2⟩
  subst e1 e2
  simp[Untyped.lookup_defn, Functor.map, Option.bind_eq_some_iff]
  exists .defn x ⟦t⟧
  apply And.intro
  apply lookup_erasure wf h1
  rfl

-- theorem erasure_well_def (wf : ⊢ G)

