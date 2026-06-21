
import Core.Typing
import Core.Util
import Core.Metatheory.Global

open LeanSubst
open Lilac

namespace Core

theorem subst_lift [RenMap T T] [RenMapId T T] [RenMapCompose T T] (σ : Subst T) :
  x < n ->
  (σ.lift n).act x = re x
:= by
  intro h; induction n generalizing x σ; cases h
  case _ n ih =>
  cases x; simp [Subst.lift]
  case _ i =>
  have lem : i < n := by omega
  replace ih := @ih i σ lem
  rw [Subst.rewrite_lift_succ, Subst.act]
  generalize zdef : σ.lift n = z at *
  simp [Subst.lift]; sorry-- rw [ih]

theorem Kinding.closed_rep :
  G&Δ ⊢ A : K ->
  ∀ (σ : Subst Ty), A[σ.lift Δ.length] = A
| var (x := x) j, σ =>
  have lem1 : x < Δ.length := Δ.indexing_length_some j
  have lem2 := subst_lift σ lem1
  by simp_all
| global h, σ => by simp
| arrow j1 j2, σ
| app j1 j2, σ
| eq j1 j2, σ =>
  let j1' := j1.closed_rep σ
  let j2' := j2.closed_rep σ
  by simp at j1'; simp at j2'; simp [*]
| all j, σ =>
  let j' := j.closed_rep σ
  sorry
  -- by simp [-rewrite_lift_n] at j'; simp [*]
  --    rw [Subst.rewrite_lift_succ] at j'; simp at j'
  --    exact j'

theorem Kinding.closed : G&[] ⊢ A : K -> ∀ (σ : Subst Ty), A[σ] = A := by
  intro j
  have lem := closed_rep j; sorry --simp [-rewrite_lift_n] at lem
  -- exact lem

theorem GlobalWf.head {G : List Global} : ⊢ (g :: G) -> GlobalWf G g := by
  intro j; cases j; case _ j => exact j

theorem GlobalWf.tail {G : List Global} : ⊢ (g :: G) -> ⊢ G := by
  intro j; cases j; case _ j _ => exact j

theorem SpineKinding.closed : {T : SpineTy} -> SpineKinding v x G tst T -> ∀ (σ : Subst Ty), T[σ] = T
| ⟨m, Ks, n, Ts, R⟩, valid (Δ := Δ) e j1 j2 j3 j4, σ => sorry
  -- have e2 : Δ.length = m := by rw [<-e]; simp
  -- have lem1 := λ (i : Fin n) => (j1 i).closed_rep σ
  -- have lem2 := j2.closed_rep σ |> cast (by rw [e2])
  -- have lem3 : Ts[σ.lift m:_] = Ts := by sorry
  --   -- apply Vec.eq_index_ext; rw [e2] at lem1
  --   -- simp [-rewrite_lift_n] at lem1; exact lem1
  -- by sorry --simp [-rewrite_lift_n] ; exact ⟨lem3, lem2⟩

theorem GlobalWf.closed_lookup_spine_type {G : List Global} :
  ⊢ G ->
  lookup_spine_type G x = some T ->
  ∀ (σ : Subst Ty), T[σ] = T
:= by
  intro wf h; unfold lookup_spine_type at h
  fun_induction lookup
  all_goals try
    case _ ih =>
      cases wf; case _ wf _ =>
      apply ih wf h
  all_goals try simp [Entry.spine_type] at h
  case _ n y K ctors tl ctors' h2 ih =>
    sorry
    -- generalize zdef : Vec.fold (lookup x tl) Option.or ctors' = z at *
    -- cases z <;> simp at h; case _ z =>
    -- generalize wdef : lookup x tl = w at *
    -- cases w <;> simp at *
    -- case _ =>
    --   sorry
    -- case _ e =>
    --   sorry
  case _ =>
    cases wf; case _ wf =>
    cases wf; case _ h1 h2 =>
    subst h
    apply SpineKinding.closed h2
  case _ =>
    cases wf; case _ wf =>
    cases wf; case _ h1 h2 =>
    subst h
    apply SpineKinding.closed h2

theorem GlobalWf.closed_lookup_spine_type_ren {G : List Global} :
  ⊢ G ->
  lookup_spine_type G x = some T ->
  ∀ (r : Ren Ty), T⟨r⟩ = T
:= sorry

theorem GlobalWf.subst_cancel_lookup_ctor? {T T' : Ty} {G : List Global} {σ : Subst Ty} :
  ⊢ G ->
  (e : T' = T[σ]) ->
  lookup_ctor? G v x T' ->
  lookup_ctor? G v x T
:= by
  intro wf e j
  simp [lookup_ctor?] at *
  generalize zdef : T.spine = z
  cases z <;> simp
  case none =>
    have lem : T'.spine = none := sorry
    rw [lem] at j; simp at j
  case some z =>
    rcases z with ⟨z, sp⟩
    have lem : T'.spine = some (z, sp[σ]) := sorry
    rw [lem] at j; simp at j; simp; exact j

theorem GlobalWf.subst_cancel_lookup_ctor?_ren {T T' : Ty} {G : List Global} {r : Ren Ty} :
  ⊢ G ->
  (e : T' = T⟨r⟩) ->
  lookup_ctor? G v x T' ->
  lookup_ctor? G v x T
:= by
  sorry

theorem extend_lemma {ℓ₁ ℓ₂ : List A} : {x : Nat} -> ℓ₁[x]? = some t -> (ℓ₁ ++ ℓ₂)[x]? = some t
| 0, h =>
  match ℓ₁ with
  | .nil => by simp at h
  | .cons a tl => by simp_all
| x + 1, h =>
  match ℓ₁ with
  | .nil => by simp at h
  | .cons a tl => extend_lemma (ℓ₁ := tl) (ℓ₂ := ℓ₂) h

theorem Kinding.extend : G&Δ₁ ⊢ A : K -> G&(Δ₁ ++ Δ₂) ⊢ A : K
| var h => var (extend_lemma h)
| global h => global h
| arrow j1 j2 => arrow j1.extend j2.extend
| all j => all j.extend
| app j1 j2 => app j1.extend j2.extend
| eq j1 j2 => eq j1.extend j2.extend

theorem Ty.data?_closed (σ : Subst Ty) : Ty.data? v G T -> Ty.data? v G T[σ] := sorry
-- | ⟨x, sp, e, j⟩ =>
--   have lem : T[σ].spine = some (x, sp[σ:_]) := by
--     sorry
--   ⟨x, sp[σ:Ty], lem, j⟩

theorem Ty.data?_closed_ren (r : Ren Ty) : Ty.data? v G T -> Ty.data? v G T⟨r⟩ := sorry

theorem Query.closed {σ : Subst Ty} (wf : ⊢ G) : {S : Vec Ty n} -> (e : S' = S[σ]) -> Query G v q S' -> Query G v q S
| .nil, e, .nil => .nil
| .cons hd tl, e, .cons j1 j2 => by
  simp at e; rw [e.1] at j1
  have lem := Query.closed wf e.2 j2
  apply VecTyping.cons _ lem
  apply GlobalWf.subst_cancel_lookup_ctor? wf rfl j1

theorem Query.closed_ren {r : Ren Ty} (wf : ⊢ G) : {S : Vec Ty n} -> (e : S' = S⟨r⟩) -> Query G v q S' -> Query G v q S
| .nil, e, .nil => .nil
| .cons hd tl, e, .cons j1 j2 => by
  simp at e; rw [e.1] at j1
  have lem := Query.closed_ren wf e.2 j2
  apply VecTyping.cons _ lem
  apply GlobalWf.subst_cancel_lookup_ctor?_ren wf rfl j1

theorem Typing.closed_type_rep :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[rep Subst.lift σ Δ.length] = t ∧ A[rep Subst.lift σ Δ.length] = A
:= by
  sorry
  -- intro j; induction j <;> intro σ
  -- case var j1 j2 => simp; apply Kinding.closed_rep j2
  -- case global j1 j2 => simp; apply Kinding.closed_rep j2
  -- case mtch j1 j2 j3 j4 j5 j6 j7 j8 ih1 ih2 ih3 ih4 =>
  --   have lem1 := λ i => (ih3 i σ).1
  --   have lem4 := λ i => (ih4 i σ).1
  --   simp; simp at lem1
  --   exact ⟨⟨(ih1 σ).1, (by funext; apply lem1), (by funext; apply lem4), (ih2 σ).1⟩, (ih2 σ).2⟩
  -- case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
  --   simp
  --   obtain ⟨q1, q2⟩ := ih1 σ
  --   obtain ⟨q3, q4⟩ := ih2 σ
  --   obtain ⟨q5, q6⟩ := ih3 σ
  --   have lem := PrefixTypeMatch.closed_rep σ q2 q6 j7
  --   exact ⟨⟨q1, q3, q5⟩, lem⟩
  -- case lam j1 j2 ih =>
  --   have lem := Kinding.closed_rep j1 σ
  --   obtain ⟨ih1, ih2⟩ := ih σ
  --   simp; exact ⟨⟨lem, ih1⟩, ⟨lem, ih2⟩⟩
  -- case app ih1 ih2 =>
  --   simp at ih1 ih2; simp
  --   obtain ⟨q1, q2, q3⟩ := ih1 σ
  --   exact ⟨⟨q1, (ih2 σ).1⟩, q3⟩
  -- case lamt ih =>
  --   simp at ih; simp
  --   apply ih σ
  -- case appt j1 j2 j3 ih =>
  --   have lem := Kinding.closed_rep j2 σ
  --   obtain ⟨ih1, ih2⟩ := ih σ
  --   simp at ih1 ih2; simp
  --   apply And.intro ⟨lem, ih1⟩
  --   subst j3
  --   conv => rhs; rw [<-ih2]; simp
  --   simp; rw [lem]
  -- case cast ih1 ih2 =>
  --   simp at ih2; simp
  --   obtain ⟨q1, q2⟩ := ih1 σ
  --   obtain ⟨q3, q4, q5⟩ := ih2 σ
  --   exact ⟨⟨q1, q3⟩, q5⟩
  -- case refl j =>
  --   simp; apply Kinding.closed_rep j
  -- case sym j ih =>
  --   simp at ih; simp
  --   obtain ⟨q1, q2, q3⟩ := ih σ
  --   exact ⟨q1, q3, q2⟩
  -- case seq ih1 ih2 =>
  --   simp at ih1 ih2; simp
  --   obtain ⟨q1, q2, q3⟩ := ih1 σ
  --   obtain ⟨q4, q5, q6⟩ := ih2 σ
  --   exact ⟨⟨q1, q4⟩, q2, q6⟩
  -- case appc ih1 ih2 =>
  --   simp at ih1 ih2; simp
  --   obtain ⟨q1, q2, q3⟩ := ih1 σ
  --   obtain ⟨q4, q5, q6⟩ := ih2 σ
  --   exact ⟨⟨q1, q4⟩, ⟨q2, q5⟩, q3, q6⟩
  -- case arrowc ih1 ih2 =>
  --   simp at ih1 ih2; simp
  --   obtain ⟨q1, q2, q3⟩ := ih1 σ
  --   obtain ⟨q4, q5, q6⟩ := ih2 σ
  --   exact ⟨⟨q1, q4⟩, ⟨q2, q5⟩, q3, q6⟩
  -- case fst ih =>
  --   simp at ih; simp
  --   obtain ⟨q1, ⟨q2, q3⟩, q4, q5⟩ := ih σ
  --   exact ⟨q1, q2, q4⟩
  -- case snd ih =>
  --   simp at ih; simp
  --   obtain ⟨q1, ⟨q2, q3⟩, q4, q5⟩ := ih σ
  --   exact ⟨q1, q3, q5⟩
  -- case allc ih =>
  --   simp at ih; simp
  --   apply ih σ
  -- case apptc j1 j2 ih1 ih2 =>
  --   simp at ih1 ih2; simp
  --   obtain ⟨q1, q2, q3⟩ := ih1 σ
  --   obtain ⟨q4, q5, q6⟩ := ih2 σ
  --   apply And.intro ⟨q1, q4⟩
  --   apply And.intro
  --   subst j1; conv => rhs; rw [<-q2]; simp
  --   simp; rw [q5]
  --   subst j2; conv => rhs; rw [<-q3]; simp
  --   simp; rw [q6]
  -- case zero j =>
  --   simp; apply Kinding.closed_rep j
  -- case choice ih1 ih2 =>
  --   simp
  --   obtain ⟨q1, q2⟩ := ih1 σ
  --   obtain ⟨q3, q4⟩ := ih2 σ
  --   exact ⟨⟨q1, q3⟩, q4⟩

theorem Typing.closed_type :
  G&[],Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[σ] = t ∧ A[σ] = A
:= by
  intro j σ
  have lem := closed_type_rep j σ; simp at lem
  exact lem

theorem Typing.closed_rep :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[rep Subst.lift σ Γ.length ◾ τ] = t
:= by
  sorry
  -- intro j; induction j <;> intro σ τ
  -- all_goals try solve | simp; try grind
  -- case var Γ x A Δ b j1 j2 =>
  --   have lem : x < Γ.length := Γ.indexing_length_some j1
  --   simp; rw [subst_lift σ lem]; simp
  -- case mtch ih1 ih2 ih3 ih4 =>
  --   simp
  --   exact ⟨ih1 _ _, (by funext; apply ih3 _ _ _), (by funext; apply ih4 _ _ _), ih2 _ _⟩
  -- case lam j1 j2 ih =>
  --   replace ih := ih σ τ; simp at ih; simp
  --   exact ih

theorem Typing.closed :
  G&Δ,[] ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[σ ◾ τ] = t
:= by
  intro j σ
  have lem := closed_rep j σ; simp at lem
  exact lem

theorem Typing.weaken_type_closed Δ :
  ⊢ G ->
  G&[],[] ⊢ t : A ->
  G&Δ,[] ⊢ t : A
:= by
  sorry
  -- intro wf j
  -- have lem1 := weaken_type_list Δ wf j; simp at lem1
  -- obtain ⟨q1, q2⟩ := closed_type j (Ren.to (· + Δ.length))
  -- rw [q1, q2] at lem1
  -- exact lem1

theorem Typing.weaken_closed Γ :
  ⊢ G ->
  G&Δ,[] ⊢ t : A ->
  G&Δ,Γ ⊢ t : A
:= by
  sorry
  -- intro wf j
  -- have lem1 := weaken_list Γ wf j; simp at lem1
  -- have lem2 := closed j (Ren.to (· + Γ.length)) +0; simp at lem2
  -- rw [lem2] at lem1
  -- exact lem1


theorem CoercionProject.extend Δ
  : CoercionProject G Δ₁ n T A -> CoercionProject G (Δ₁ ++ Δ) n T A
| fst_app j => fst_app j.extend
| snd_app j => snd_app j.extend
| fst_arrow j => fst_arrow j.extend
| snd_arrow j => snd_arrow j.extend

theorem PatternBinders.extend Δ
  : PatternBinders G Δ₁ m S p ζ ξ -> PatternBinders G (Δ₁ ++ Δ) m S p ζ ξ
| zero => zero
| succ j1 j2 e1 e2 e3 j3 => succ j1 (λ i => (j2 i).extend) e1 e2 e3 (j3.extend _)

theorem Typing.extend Δ Γ : G&Δ₁,Γ₁ ⊢ t : A -> G&(Δ₁ ++ Δ),(Γ₁ ++ Γ) ⊢ t : A
| var (x := x) j1 j2 => var (extend_lemma j1) j2.extend
| defn j1 j2 => defn j1 j2.extend
| spctor j1 e1 e2 j2 j3 j4 j5 j6 => sorry --spctor j1 e1 e2 (λ i => (j2 i).extend) (λ i => (j3 i).extend _ _) j4 j5
| mtch j1 j2 j3 j4 j5 =>
  sorry
  -- let j4' := (λ i => (j4 i).extend Δ Γ ▸ congr 1; grind)
  -- mtch (λ i => (j1 i).extend _ _) j2 (λ i => (j3 i).extend _) j4' j5
| lam (A := A) j1 j2 => lam j1.extend (j2.extend _ _)
| app j1 j2 => app (j1.extend _ _) (j2.extend _ _)
| lamt j1 j2 => lamt j1.extend (j2.extend Δ Γ⟨.succ Ty⟩ ▸ simp)
| appt (P := P) j1 j2 e => appt (j1.extend _ _) j2.extend e
| refl j1 => refl j1.extend
| cast j1 j2 j3 e => cast j1.extend (j2.extend _ _) (j3.extend _ _) e
| prj j1 j2 => prj (j1.extend _ _) (j2.extend _)
| allc j1 => allc (j1.extend Δ Γ⟨.succ Ty⟩ ▸ simp)
| apptc j1 j2 e1 e2 => apptc (j1.extend _ _) (j2.extend _ _) e1 e2

theorem GlobalWf.closed_lookup_defn {G : List Global} :
  ⊢ G ->
  lookup_defn G x = some (A, t) ->
  (∀ (σ : Subst Ty), A[σ] = A) ∧ (∀ (σ : Subst Term), t[σ] = t) ∧ (∀ (σ : Subst Ty), t[σ] = t)
:= by
  intro wf h
  unfold lookup_defn at h; simp at h
  replace h := Option.bind_eq_some_iff.1 h
  rcases h with ⟨e, h⟩
  cases e <;> simp at h; case _ z B s =>
  rcases h with ⟨h, e1, e2⟩; subst e1 e2
  have lem := EntryWf.from_lookup wf h
  cases lem; case _ j1 j2 lem =>
  sorry

theorem GlobalWf.closed_lookup_defn_ren {G : List Global} :
  ⊢ G ->
  lookup_defn G x = some (A, t) ->
  (∀ (r : Ren Ty), A⟨r⟩ = A) ∧ (∀ (r : Ren Term), t⟨r⟩ = t) ∧ (∀ (r : Ren Ty), t⟨r⟩ = t)
:= by
  sorry

-- theorem Kinding.closed_lifting_lemma :
--   ∀ Δ', ⊢ G ->
--   G&Δ ⊢ T : K ->
--   (G&(Δ' ++ Δ) ⊢ T[Ren.to (λ x => (x + Δ'.length))] : K)
-- := by
--   sorry
-- intro Δ' wf j
-- apply @List.reverse_ind (T := Kind)
--   (motive := λ Δ' => ∀ G Δ T K,  ⊢ G -> G&Δ ⊢ T : K -> (G&(Δ' ++ Δ) ⊢ T[Ren.to (λ x => (x + Δ'.length))] : K))
--   Δ'
--   (by intro G Δ T K wf j;
--       have lem : (Ren.to (λ x => x)) = Subst.id (T := Ty) := by rfl
--       simp; rw[lem]; simp; assumption)
--   (by intro K' Δ' ih G Δ T K wf j
--       replace j := Kinding.weaken K' j
--       replace ih := ih G ([K'] ++ Δ) T[+1] K wf j
--       simp at *
--       have lem : ((+1 ∘ Ren.to (T := Ty) (fun x => x + Δ'.length))) = Ren.to (T := Ty) (fun x => x + Δ'.length + 1) := by
--          clear ih j wf;
--          have e := Ren.add_compose_distributes (T := Ty) (y := Δ'.length) (z := 1); rw[e]; simp;
--          replace e := Ren.add_one_commutes (T := Ty) (y := Δ'.length); simp at e; rw[e]
--       rw[lem] at ih; apply ih)
--   G Δ T K wf j

-- theorem Kinding.closed_arbitrary_weakening : ∀ Δ',  ⊢ G ->  G&[] ⊢ T : K ->  G&Δ' ⊢ T : K := by
-- intro Δ' wf j
-- have lem1 := Kinding.closed j
-- have lem2 := Kinding.closed_lifting_lemma Δ' wf j
-- simp at *
-- replace lem1 := lem1 (Ren.to (λ x => x + Δ'.length))
-- rw[lem1] at lem2
-- apply lem2

end Core
