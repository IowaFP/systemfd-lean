import Core.Term
import Core.Reduction
import Core.Typing

open Lilac
open LeanSubst

namespace Core

theorem split_all_or_left : ∀ {n} {A B : Fin n -> Prop}, (∀ i, A i ∨ B i) -> (∀ i, A i) ∨ (∃ i, B i)
| 0, _, _, _ => Or.inl (Fin.elim0 ·)
| n + 1, _, _, h =>
  have h' := λ (i : Fin n) => h i.succ
  have lem := @split_all_or_left n _ _ h'
  match lem with
  | Or.inl lem' =>
    match h 0 with
    | Or.inl h2 => Or.inl (Fin.cases h2 lem')
    | Or.inr h2 => Or.inr ⟨0, h2⟩
  | Or.inr ⟨k, lem'⟩ => Or.inr ⟨k.succ, lem'⟩

-- ∀ (i : Fin m✝), G&Δ,Γ ⊢ ss i : S✝ i
-- j2 : ∀ (i : Fin m✝), Ty.datatype? G (S✝ i)

@[simp]
def Constructor.query : Vec Constructor n -> Vec String n
| .nil => .nil
| .cons (s, _, _) tl => .cons s (Constructor.query tl)

theorem Constructor.query_nil : {c : Vec Constructor 0} -> query c = .nil -> c = .nil
| .nil, _ => rfl

theorem Constructor.query_cons {qs : Vec _ _} :
  {c : Vec Constructor (n + 1)} ->
  query c = q::qs ->
  ∃ As ts, ∃ (cs : Vec _ _), c = (q,As,ts)::cs ∧ query cs = qs
| .cons (s, As, ts) tl, e =>
  have lem : s = q ∧ query tl = qs := by simp at e; exact e
  ⟨As, ts, tl, by rw [lem.1]; rfl, lem.2⟩

theorem progress_match_ctors {S ss : Fun.Vec _ _} :
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss i : S i) ->
  (∀ (i : Fin m), Ty.datatype? G (S i)) ->
  (∀ (i : Fin m), Value G (ss i)) ->
  ∃ ctors, Term.IsData ss.to ctors ∧ Query G (Constructor.query ctors) S.to
:= by
  intro h1 h2 h3
  generalize zdef : ss.to = z at *
  induction z
  case nil => sorry
  case cons n hd tl ih =>
    have lem1 := h1 0
    have lem2 := h2 0
    have lem3 := h3 0

    sorry

theorem query_match_implies_pattern_match :
  Constructor.query c = q ->
  Query.Match q p ->
  Pattern.Match c p
| e, .nil => Pattern.Match.nil |> cast (by rw [Constructor.query_nil e])
| e, .cons (ts := Bs) (n := n) tl =>
  let ⟨As, ts, cs, h1, h2⟩ := Constructor.query_cons e
  let tl' := query_match_implies_pattern_match h2 tl
  by rw [h1]; apply Pattern.Match.cons tl'

theorem progress : G&Δ,Γ ⊢ t : T -> Γ = [] -> Value G t ∨ ∃ t', G ⊢ t ~> t'
| .dctor j1 j2 j3 j4 j5, e => Or.inl Value.dctor
| .mtch (ss := ss) j1 j2 j3 j4 j5, e =>
  let j1' := λ i => progress (j1 i) e
  match split_all_or_left j1' with
  | Or.inl vs =>
    let ⟨ctors, h1, h2⟩ := progress_match_ctors j1 j2 vs
    let ⟨i, h3⟩ := j5 h2
    let lem1 := query_match_implies_pattern_match rfl h3
    let σ := Constructor.subst ctors
    Or.inr ⟨_, .data_match (σ := σ) h1 lem1 rfl⟩
  | Or.inr ⟨i, t', r⟩ =>
    let ss' := Fun.Vec.update ss t' i
    let r' : G ⊢ ss i ~> ss' i := by subst ss'; simp; exact r
    Or.inr ⟨_, .match_congr i r' Fun.Vec.update_neq⟩
| .lam j1 j2, e => Or.inl Value.lam
| .app j1 j2 j3, e => sorry
| .lamt j1 j2, e => Or.inl Value.lamt
| .appt j1 j2 j3, e => sorry
| .refl j, e => Or.inl Value.refl
| .cast j1 j2 j3 e1, e2 => sorry
| .prj j1 j2, e => sorry
| .allc j1, e => sorry
| .apptc j1 j2 e1 e2, e3 => sorry
| .zero j, e => sorry
| _, _ => sorry

-- theorem progress_lemma :
--   ⊢ G ->
--   Γ = [] ->
--   G&Δ,Γ ⊢ t : T ->
--   Value G t ∨ t = `0 ∨ ∃ t', G ⊢ t ~> t' := by
-- intro wf e j
-- induction j
-- case var => subst e; simp at *
-- case global =>
--   subst e

--   sorry
-- case mtch =>
--   subst e
--   sorry
-- case guard =>
--   subst e
--   sorry
-- case lam => apply Or.inl; apply Value.lam
-- case lamt => apply Or.inl; apply Value.lamt
-- case zero => apply Or.inr; apply Or.inl; rfl
-- case refl => apply Or.inl; apply Value.refl
-- case app b _ _ _ _ _ _ _ ih1 ih2 =>
--   cases b
--   case _ =>
--     cases ih2 e
--     case _ => sorry
--     case _ => sorry
--   case _ =>
--     sorry

-- case appt => sorry
-- case cast t A _ _ _ _ j _ ih =>
--   cases ih e
--   case _ h =>
--     have lem := refl_is_val j h
--     cases lem;
--     case _ lem =>
--       rcases lem with ⟨e1, e2⟩; subst e1; subst e2
--       apply Or.inr; apply Or.inr; exists t; apply Red.cast
--     case _ lem =>
--       rcases lem with ⟨c1, c2, e⟩; subst e
--       apply Or.inr; apply Or.inr
--       exists (t ▹ c1) `+  (t ▹ c2)
--       apply Red.ctor2_map2; simp; simp
--   case _ lem =>
--      cases lem
--      case _ h => subst h; apply Or.inr; apply Or.inr; exists `0; apply Red.ctor2_absorb2 (v := .cast); simp
--      case _ h =>
--        rcases h with ⟨c', h⟩
--        apply Or.inr; apply Or.inr; exists (t ▹ c')
--        apply Red.ctor2_congr2 (by simp) h

-- case sym ih =>
--   cases ih e
--   case _ ih => sorry
--   case _ ih =>
--     cases ih
--     case _ ih => sorry
--     case _ ih => sorry

-- case seq ih1 ih2 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry


-- case appc ih1 ih2 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case arrowc ih1 ih2 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case fst ih1 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case snd ih1 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case allc Γ _ ih1 =>
--   have e' : List.map (λ x => x[+1]) Γ = [] := by rw[e]; simp
--   cases ih1 e'
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case apptc ih1 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

-- case choice ih1 ih2 =>
--   cases ih1 e
--   case _ ih1 => sorry
--   case _ ih1 =>
--     cases ih1
--     case _ ih1 => sorry
--     case _ ih1 => sorry

end Core
