import Core.Term
import Core.Reduction
import Core.Typing

open Lilac
open LeanSubst

namespace Core

@[grind →]
theorem spctor_inversion :
  ¬ v = .openm ->
  G&Δ,Γ ⊢ Term.spctor v s tys ts : T ->
  T.spine.isSome
:= by
  sorry

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

@[simp]
def Constructor.query : Vec Constructor n -> Vec String n
| .nil => .nil
| .cons ⟨s, _, _, _, _⟩ tl => .cons s (Constructor.query tl)

theorem Constructor.query_nil : {c : Vec Constructor 0} -> query c = .nil -> c = .nil
| .nil, _ => rfl

-- theorem Constructor.query_cons {qs : Vec _ _} :
--   {c : Vec Constructor (n + 1)} ->
--   query c = q::qs ->
--   ∃ As ts, ∃ (cs : Vec _ _), c = (q,As,ts)::cs ∧ query cs = qs
-- | .cons (s, As, ts) tl, e =>
--   have lem : s = q ∧ query tl = qs := by simp at e; exact e
--   ⟨As, ts, tl, by rw [lem.1]; rfl, lem.2⟩

-- theorem progress_match_ctors_head {ctors : Vec _ n} :
--   G&Δ,Γ ⊢ s : S ->
--   Ty.datatype? G S ->
--   Value G s ->
--   Term.IsData .cdata ss ctors ->
--   Query G (Constructor.query ctors) SS ->
--   ∃ ctors, Term.IsData SpCtorVariant.cdata (s :: ss) ctors ∧ Query G (Constructor.query ctors) (S :: SS)
-- | .spctor (v := .cdata) (ctor := c) (As := As) (ts := ts) j1 j2 j3 j4 j5 j6, h2, .spctor h, h4, h5 =>
--   let ts' := Vec.to_list ts.to
--   let lem1 := @Term.IsData.cons .cdata ts' n ss ctors c As _ ts rfl h4
--   let lem2 : Ty.ctor? G c S := by {
--     simp [Ty.datatype?, Ty.HeadVariable] at h2
--     simp [Ty.ctor?]
--     sorry -- obvious, should rework global stuff so that we can just grind this
--   }
--   let lem3 := @Query.cons G _ (Constructor.query ctors) SS c S lem2 h5
--   ⟨⟨c, As, ts'⟩::ctors, lem1, lem3⟩
-- | .spctor (v := .odata) (ctor := c) (As := As) (ts := ts) j1 j2 j3 j4 j5 j6, h2, .spctor h, h4, h5 =>
--   sorry -- impossible by j6 and h2
-- | .refl j, h2, .refl, h4, h5 => by simp [Ty.datatype?, Ty.HeadVariable, Ty.spine] at h2
-- | .lam j1 j2, h2, .lam, h4, h5 => by simp [Ty.datatype?, Ty.HeadVariable, Ty.spine] at h2
-- | .lamt j1 j2, h2, .lamt, h4, h5 => by simp [Ty.datatype?, Ty.HeadVariable, Ty.spine] at h2

-- theorem progress_match_ctors :
--   {m : Nat} ->
--   {S ss : Vec _ m} ->
--   (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
--   (∀ (i : Fin m), Ty.datatype? G S[i]) ->
--   (∀ (i : Fin m), Value G ss[i]) ->
--   ∃ ctors, Term.IsData .cdata ss ctors ∧ Query G (Constructor.query ctors) S
-- | 0, .nil, .nil, h1, h2, h3 => ⟨.nil, Term.IsData.nil, Query.nil⟩
-- | m + 1, .cons Shd S, .cons shd s, h1, h2, h3 =>
--   let h1' : ∀ (i : Fin m), G&Δ,Γ ⊢ s[i] : S[i] := λ i => h1 i.succ
--   let h2' : ∀ (i : Fin m), Ty.datatype? G S[i] := λ i => h2 i.succ
--   let h3' : ∀ (i : Fin m), Value G s[i] := λ i => h3 i.succ
--   let ⟨ctors, q1, q2⟩ := progress_match_ctors h1' h2' h3'
--   progress_match_ctors_head (h1 0) (h2 0) (h3 0) q1 q2

-- theorem query_match_implies_pattern_match :
--   Constructor.query c = q ->
--   Query.Match q p ->
--   Pattern.Match c p
-- | e, .nil => Pattern.Match.nil |> cast (by rw [Constructor.query_nil e])
-- | e, .cons (ts := Bs) (n := n) tl =>
--   let ⟨As, ts, cs, h1, h2⟩ := Constructor.query_cons e
--   let tl' := query_match_implies_pattern_match h2 tl
--   by rw [h1]; apply Pattern.Match.cons tl'

theorem progress :
  G&Δ,Γ ⊢ t : T ->
  Γ = [] ->
  Value G t ∨ ∃ t', G ⊢ t ~> t'
| .defn j1 j2, e => sorry
| .spctor (v := .data .cls) j1 j2 j3 j4 j5 j6 j7, e => Or.inl $ Value.spctor (by simp)
| .spctor (v := .data .opn) j1 j2 j3 j4 j5 j6 j7, e => Or.inl $ Value.spctor (by simp)
| .spctor (v := .openm) (ts := ts) j1 j2 j3 j4 j5 j6 j7, e =>
  let j4' := λ i => progress (j4 i) e
  match split_all_or_left j4' with
  | Or.inl vs =>
    sorry
  | Or.inr ⟨i, t', r⟩ =>
    let ts' := Fun.Vec.update ts t' i
    let r' : G ⊢ ts i ~> ts' i := by subst ts'; simp; exact r
    Or.inr ⟨_, .openm_congr i r' Fun.Vec.update_neq⟩
| .mtch (m := m) (S := S) (ss := ss) j1 j2 j3 j4 j5, e =>
  let j1' := λ i => progress (j1 i) e
  match split_all_or_left j1' with
  | Or.inl vs => sorry
    -- let j1' : ∀ (i : Fin m), G&Δ,Γ ⊢ ss.to[i] : S.to[i] := j1 |> cast (by simp)
    -- let j2' : ∀ (i : Fin m), Ty.datatype? G S.to[i] := j2 |> cast (by simp)
    -- let vs' : ∀ (i : Fin m), Value G ss.to[i] := vs |> cast (by simp)
    -- let ⟨ctors, h1, h2⟩ := progress_match_ctors j1' j2' vs'
    -- let ⟨i, h3⟩ := j5 h2
    -- let lem1 := query_match_implies_pattern_match rfl h3
    -- let σ := Constructor.subst ctors
    -- Or.inr ⟨_, .data_match (σ := σ) h1 lem1 rfl⟩
  | Or.inr ⟨i, t', r⟩ =>
    let ss' := Fun.Vec.update ss t' i
    let r' : G ⊢ ss i ~> ss' i := by subst ss'; simp; exact r
    Or.inr ⟨_, .match_congr i r' Fun.Vec.update_neq⟩
| .lam j1 j2, e => Or.inl Value.lam
| .app j1 j2, e =>
  match progress j1 e with
  | Or.inl v =>
    match v, j1 with
    | .lam, .lam j3 j4 => Or.inr ⟨_, .beta⟩
    | .spctor h, j3 => by grind
  | Or.inr ⟨f', r⟩ => Or.inr ⟨_, .app_congr r⟩
| .lamt j1 j2, e => Or.inl Value.lamt
| .appt j1 j2 j3, e =>
  match progress j1 e with
  | Or.inl v =>
    match v, j1 with
    | .lamt, .lamt j3 j4 => Or.inr ⟨_, .betat⟩
    | .spctor h, j3 => by grind
  | Or.inr ⟨f', r⟩ => Or.inr ⟨_, .ctor1_congr r⟩
| .refl j, e => Or.inl Value.refl
| .cast (R := R) (t := t) j1 j2 j3 e1, e2 =>
  match progress j2 e2 with
  | Or.inl v =>
    match v, j2 with
    | .refl, .refl j4 => Or.inr ⟨t, .cast⟩
    | .spctor h, j4 => by grind
  | Or.inr ⟨c', r⟩ => Or.inr ⟨.cast R c' t, .cast_congr r⟩
| .prj j1 j2, e =>
  match progress j1 e with
  | Or.inl v =>
    match v, j1, j2 with
    | .refl, .refl j3, .fst_app h => Or.inr ⟨_, .prj_fst_app⟩
    | .refl, .refl j3, .snd_app h => Or.inr ⟨_, .prj_snd_app⟩
    | .refl, .refl j3, .fst_arrow h => Or.inr ⟨_, .prj_fst_arr⟩
    | .refl, .refl j3, .snd_arrow h => Or.inr ⟨_, .prj_snd_arr⟩
    | .spctor h, j3, .fst_app _
    | .spctor h, j3, .snd_app _
    | .spctor h, j3, .fst_arrow _
    | .spctor h, j3, .snd_arrow _ => by grind
  | Or.inr ⟨t', r⟩ => Or.inr ⟨_, .ctor1_congr r⟩
| .allc j1, e =>
  match progress j1 (e |> cast (by grind)) with
  | Or.inl v =>
    match v, j1 with
    | .refl, .refl j2 => Or.inr ⟨_, .allc⟩
    | .spctor h, j2 => by grind
  | Or.inr ⟨c', r⟩ => Or.inr ⟨_, .allc_congr r⟩
| .apptc j1 j2 e1 e2, e3 =>
  match progress j1 e3, progress j2 e3 with
  | Or.inl v1, Or.inl v2 =>
    match v1, v2, j1, j2 with
    | .refl, .refl, .refl j3, .refl j4 => Or.inr ⟨_, .apptc⟩
    | .spctor h, _, j3, j4 => by grind
    | _, .spctor h, j3, j4 => by grind
  | Or.inr ⟨f', r⟩, _ => Or.inr ⟨_, .apptc_congr1 r⟩
  | _, Or.inr ⟨a', r⟩ => Or.inr ⟨_, .apptc_congr2 r⟩
-- | _, _ => sorry

end Core
