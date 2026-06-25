import Core.Term
import Core.Reduction
import Core.Typing
import Core.Metatheory.Closed

open Lilac
open LeanSubst

namespace Core

@[grind →]
theorem spctor_inversion :
  ¬ v = .openm ->
  G&Δ,Γ ⊢ Term.spctor v s As Bs ts : T ->
  T.spine.isSome
:= by
  intro j1 j2
  cases j2; case _ j2 j3 j4 j5 j6 j7 j8 j9 =>
  cases v <;> simp at j1; case _ c =>
  -- replace j4 := j4 c rfl; subst j8
  sorry

theorem lookup_ctor?_subst (σ : Subst Ty) : lookup_ctor? G c x R -> lookup_ctor? G c x R[σ] := by
  intro h; unfold lookup_ctor? at *
  generalize zdef : R.spine = z at *
  cases z <;> simp at h; case _ z =>
  rcases z with ⟨z, sp⟩; simp at h
  have lem : R[σ].spine = some (z, sp[σ]) := sorry
  rw [lem]; simp [*]

theorem lookup_ctor?_data?_force_dataconst (σ : Subst Ty) :
  lookup_ctor? G v1 x R ->
  Ty.data? v2 G R[σ] = true ->
  v2 = v1
:= by
  intro h1 h2
  unfold lookup_ctor? at h1
  unfold Ty.data? at h2
  generalize zdef : R.spine = z at *
  cases z; simp at *; case _ z =>
  rcases z with ⟨z, sp⟩; simp at *
  have lem : R[σ].spine = some (z, sp[σ]) := sorry
  rw [lem] at h2; simp at h2
  unfold is_data at h2
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

theorem PatternBinders.implies_pattern_typing :
  PatternBinders G Δ m S p ζ ξ ->
  PatternTyping G Δ p S
| .zero => by cases S; cases p; apply VecTyping.nil
| .succ h1 h2 h3 h4 h5 tl =>
  let tl' := tl.implies_pattern_typing
  let lem := .valid h1 h2 h5
  .cons lem tl'

@[simp]
def Constructor.query : Vec Constructor n -> Vec String n
| .nil => .nil
| .cons ⟨s, _, _, _, _⟩ tl => .cons s (Constructor.query tl)

theorem Constructor.query_nil : {c : Vec Constructor 0} -> query c = .nil -> c = .nil
| .nil, _ => rfl

theorem Constructor.query_cons {qs : Vec _ _} :
  {c : Vec Constructor (n + 1)} ->
  query c = q::qs ->
  ∃ na nt As ts, ∃ (cs : Vec _ _), c = ⟨q,na,As,nt,ts⟩::cs ∧ query cs = qs
| .cons ⟨s, na, As, nt, ts⟩ tl, e =>
  have lem : s = q ∧ query tl = qs := by simp at e; exact e
  ⟨na, nt, As, ts, tl, by rw [lem.1], lem.2⟩

theorem progress_match_ctors_head {ctors : Vec _ n} :
  G&Δ,Γ ⊢ s : S ->
  Ty.data? cv G S ->
  Value G s ->
  VecConstructorTyping G Δ Γ cv ctors SS ->
  Term.IsData cv ss ctors ->
  Query G cv (Constructor.query ctors) SS ->
  ∃ ctors, VecConstructorTyping G Δ Γ cv ctors (S::SS)
    ∧ Term.IsData cv (s::ss) ctors
    ∧ Query G cv (Constructor.query ctors) (S::SS)
| .spctor (v := .data cv') (x := x) (m1 := na) (As := As) (m2 := nb) (Bs := Bs) (n := nt) (ts := ts) j1 j2 j3 j4 j5 j6 j7 j8 j9
, h2, .spctor h, h4, h5, h6 =>
  have lem1 : cv = cv' := lookup_ctor?_data?_force_dataconst
    (List.map su (As.list ++ Bs.list).reverse ++ Subst.id Ty) (j7 _ rfl) (by subst j3; apply h2)
  let ctors' := ⟨x, na, As, nb, Bs, nt, ts.to⟩::ctors
  have lem2hd : ConstructorTyping G Δ Γ cv ⟨x, na, As, nb, Bs, nt, ts.to⟩ S :=
    .valid (x := x) j1 (j7 cv' rfl |> cast (by simp [lem1])) j2 j3 (j4 |> cast (by simp)) j5 (j6 |> cast (by simp [Vec.get_to]))
  have lem2 : VecConstructorTyping G Δ Γ cv ctors' (S :: SS) := VecTyping.cons lem2hd h4
  have lem3 : Term.IsData cv (.spctor (.data cv') x As Bs ts::ss) ctors' :=
    Term.IsData.cons h5 (by simp [lem1]) rfl
  have lem4 : Query G cv (Constructor.query ctors') (S::SS) :=
    VecTyping.cons (by simp; subst j3; rw [lem1]; apply lookup_ctor?_subst _ (j7 _ rfl)) h6
  ⟨ctors', lem2, lem3, lem4⟩
| .refl j, h2, .refl, h4, h5, h6 => by simp [Ty.data?, Ty.spine] at h2
| .lam j1 j2, h2, .lam, h4, h5, h6 => by simp [Ty.data?, Ty.spine] at h2
| .lamt j1 j2, h2, .lamt, h4, h5, h6 => by simp [Ty.data?, Ty.spine] at h2

theorem progress_match_ctors :
  {m : Nat} ->
  {S ss : Vec _ m} ->
  (∀ (i : Fin m), G&Δ,Γ ⊢ ss[i] : S[i]) ->
  (∀ (i : Fin m), Ty.data? c G S[i]) ->
  (∀ (i : Fin m), Value G ss[i]) ->
  ∃ ctors, VecConstructorTyping G Δ Γ c ctors S
    ∧ Term.IsData c ss ctors
    ∧ Query G c (Constructor.query ctors) S
| 0, .nil, .nil, h1, h2, h3 => ⟨.nil, .nil, Term.IsData.nil, .nil⟩
| m + 1, .cons Shd S, .cons shd s, h1, h2, h3 =>
  let h1' : ∀ (i : Fin m), G&Δ,Γ ⊢ s[i] : S[i] := λ i => h1 i.succ
  let h2' : ∀ (i : Fin m), Ty.data? c G S[i] := λ i => h2 i.succ
  let h3' : ∀ (i : Fin m), Value G s[i] := λ i => h3 i.succ
  let ⟨ctors, q1, q2, q3⟩ := progress_match_ctors h1' h2' h3'
  progress_match_ctors_head (h1 0) (h2 0) (h3 0) q1 q2 q3

theorem query_match_implies_pattern_match (G : List Global) {n : Nat} {c q p Ts : Vec _ n} :
  VecConstructorTyping G Δ Γ v c Ts ->
  PatternTyping G Δ p Ts ->
  Constructor.query c = q ->
  Query.Match q p ->
  Pattern.Match c p
| .nil, .nil, e, .nil => .nil
| .cons ctj cttl, .cons ptj pttl, e, .cons e1 qmtl =>
  let ⟨na, nt, As, ts', ctl', h1, h2⟩ := Constructor.query_cons e
  by {
    injection h1 with he0 he1 he2; clear he0; subst he1 he2
    rcases e1 with ⟨na', As', nb', he0⟩; subst he0
    cases ctj; case _ e1 _ _ =>
    cases ptj; case _ e2 _ _ =>
    rw [e2] at e1
    injection e1 with e1
    cases e1
    apply Pattern.Match.cons
    apply query_match_implies_pattern_match G cttl pttl h2 qmtl
    rfl; rfl
  }

theorem progress (oe : OpenExhaustive G) :
  G&Δ,Γ ⊢ t : T ->
  Γ = [] ->
  Value G t ∨ ∃ t', G ⊢ t ~> t'
| .defn j1 j2, e => Or.inr ⟨_, .defn j1⟩
| .spctor (v := .data .cls) j1 j2 j3 j4 j5 j6 j7 j j9, e => Or.inl $ Value.spctor (by simp)
| .spctor (v := .data .opn) j1 j2 j3 j4 j5 j6 j7 j8 j9, e => Or.inl $ Value.spctor (by simp)
| @Typing.spctor G Δ Γ m1 m2 n x .openm Ks1 Ks2 Ts Ts' R R' As Bs ts j1 j2 j3 j4 j5 j6 j7 j8 j9, e =>
  let j6' := λ i => progress oe (j6 i) e
  match split_all_or_left j6' with
  | Or.inl vs =>
    sorry
  --   let Ts' : Vec Ty n := Vec.map (·[τ]) Ts
  --   let j1' : ∀ (i : Fin n), G&Δ,Γ ⊢ ts.to[i] : Ts'[i] := j4 |> cast (by subst Ts'; simp)
  --   let j2' : ∀ (i : Fin n), Ty.data? .opn G Ts'[i] := (j6 rfl) |> cast (by subst Ts'; simp)
  --   let vs' : ∀ (i : Fin n), Value G ts.to[i] := vs |> cast (by simp)
  --   let ⟨ctors, h1, h2, h3⟩ := progress_match_ctors j1' j2' vs'
  --   let lem1 : lookup x G = some (.openm x ⟨m, Ks, n, Ts, R⟩) := sorry
  --   let ⟨i, b, p, lem2, lem3⟩ := oe (q := Constructor.query ctors) lem1 j2 j3 (by congr) (h3 |> cast (by congr))
  --   let lem4 : PatternTyping G Δ p Ts' := sorry
  --   let lem5 := query_match_implies_pattern_match G h1 lem4 rfl lem3
  --   let σ := Constructor.subst ctors
  --   Or.inr ⟨_, .openm_match (σ := σ) h2 lem2 j3 lem5 rfl⟩
  | Or.inr ⟨i, t', r⟩ =>
    let ts' := Vec.set ts.to i t'
    let r' : G ⊢ ts i ~> ts'[i] := by subst ts'; simp; exact r
    Or.inr ⟨_, .openm_congr i r' (by {
      intro j h; simp [ts']
      have lem := Vec.get_set_neq (Ne.symm h) (v := ts.to) (x := t')
      rw [Vec.get_to] at lem; rw [<-lem]; simp [getElem]
    })⟩
| .mtch (m := m) (S := S) (ss := ss) j1 j2 j3 j4 j5, e =>
  let j1' := λ i => progress oe (j1 i) e
  match split_all_or_left j1' with
  | Or.inl vs =>
    let j1' : ∀ (i : Fin m), G&Δ,Γ ⊢ ss.to[i] : S.to[i] := j1 |> cast (by simp [Vec.get_to])
    let j2' : ∀ (i : Fin m), Ty.data? .cls G S.to[i] := j2 |> cast (by simp [Vec.get_to])
    let vs' : ∀ (i : Fin m), Value G ss.to[i] := vs |> cast (by simp [Vec.get_to])
    let ⟨ctors, h1, h2, h3⟩ := progress_match_ctors j1' j2' vs'
    let ⟨i, h4⟩ := j5 h3
    let h5 := PatternBinders.implies_pattern_typing (j3 i)
    let lem1 := query_match_implies_pattern_match G h1 h5 rfl h4
    let ℓ := Constructor.subst ctors
    Or.inr ⟨_, .data_match h2 lem1 rfl⟩
  | Or.inr ⟨i, t', r⟩ =>
    let ss' := Vec.set ss.to i t'
    let r' : G ⊢ ss i ~> ss'[i] := by subst ss'; simp; exact r
    Or.inr ⟨_, .match_congr i r' (by {
      intro j h; simp [ss']
      have lem := Vec.get_set_neq (Ne.symm h) (v := ss.to) (x := t')
      rw [Vec.get_to] at lem; rw [<-lem]; simp [getElem]
    })⟩
| .lam j1 j2, e => Or.inl Value.lam
| .app j1 j2, e =>
  match progress oe j1 e with
  | Or.inl v =>
    match v, j1 with
    | .lam, .lam j3 j4 => Or.inr ⟨_, .beta⟩
    | .spctor h, j3 => by grind
  | Or.inr ⟨f', r⟩ => Or.inr ⟨_, .app_congr r⟩
| .lamt j1 j2, e => Or.inl Value.lamt
| .appt j1 j2 j3, e =>
  match progress oe j1 e with
  | Or.inl v =>
    match v, j1 with
    | .lamt, .lamt j3 j4 => Or.inr ⟨_, .betat⟩
    | .spctor h, j3 => by grind
  | Or.inr ⟨f', r⟩ => Or.inr ⟨_, .ctor1_congr r⟩
| .refl j, e => Or.inl Value.refl
| .cast (R := R) (t := t) j1 j2 j3 e1, e2 =>
  match progress oe j2 e2 with
  | Or.inl v =>
    match v, j2 with
    | .refl, .refl j4 => Or.inr ⟨t, .cast⟩
    | .spctor h, j4 => by grind
  | Or.inr ⟨c', r⟩ => Or.inr ⟨.cast R c' t, .cast_congr r⟩
| .prj j1 j2, e =>
  match progress oe j1 e with
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
  match progress oe j1 (e |> cast (by grind)) with
  | Or.inl v =>
    match v, j1 with
    | .refl, .refl j2 => Or.inr ⟨_, .allc⟩
    | .spctor h, j2 => by grind
  | Or.inr ⟨c', r⟩ => Or.inr ⟨_, .allc_congr r⟩
| .apptc j1 j2 e1 e2, e3 =>
  match progress oe j1 e3, progress oe j2 e3 with
  | Or.inl v1, Or.inl v2 =>
    match v1, v2, j1, j2 with
    | .refl, .refl, .refl j3, .refl j4 => Or.inr ⟨_, .apptc⟩
    | .spctor h, _, j3, j4
    | _, .spctor h, j3, j4 => by grind
  | Or.inr ⟨f', r⟩, _ => Or.inr ⟨_, .apptc_congr1 r⟩
  | _, Or.inr ⟨a', r⟩ => Or.inr ⟨_, .apptc_congr2 r⟩
-- | _, _ => sorry

end Core
