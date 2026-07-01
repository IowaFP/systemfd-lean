
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
  rw [Subst.rewrite_lift_succ]
  generalize zdef : σ.lift n = z at *
  simp [Subst.lift]; rw [ih]; simp

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
  by simp [-Subst.rewrite_lift_k] at j'; simp [*]
     rw [Subst.rewrite_lift_succ] at j'; simp at j'
     exact j'

theorem Kinding.closed : G&[] ⊢ A : K -> ∀ (σ : Subst Ty), A[σ] = A := by
  intro j
  have lem := closed_rep j
  simp [-Subst.rewrite_lift_k] at lem
  exact lem

theorem GlobalWf.head {G : List Global} : ⊢ (g :: G) -> GlobalWf G g := by
  intro j; cases j; case _ j => exact j

theorem GlobalWf.tail {G : List Global} : ⊢ (g :: G) -> ⊢ G := by
  intro j; cases j; case _ j _ => exact j

theorem SpineKinding.closed : {T : SpineTy} -> SpineKinding v x G tst T -> ∀ (σ : Subst Ty), T[σ] = T
| ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩, valid (Δ := Δ) e j1 j2 j3 j4, σ =>
  have e2 : Δ.length = m1 + m2 := by rw [<-e]; simp; omega
  have j1' := λ (i : Fin n) => (j1 i).closed_rep σ
  have j2' := j2.closed_rep σ |> cast (by rw [e2])
  have lem : Ts[σ.lift (m1 + m2)] = Ts := by
    apply Vec.ext_get; intro i; rw [<-e2, <-j1' i]; grind
  by simp [-Subst.rewrite_lift_k, lem, j2']

theorem GlobalWf.closed_lookup_spine_type {G : List Global} :
  ⊢ G ->
  lookup_spine_type v G x = some T ->
  ∀ (σ : Subst Ty), T[σ] = T
:= by
  intro wf h; unfold lookup_spine_type at h
  generalize zdef : lookup x G = z at *
  cases z <;> simp at *; case _ z =>
  have lem := EntryWf.from_lookup wf zdef
  cases z <;> simp [Entry.spine_type] at h
  case ctor =>
    cases lem; case _ j1 j2 j3 j4 =>
    cases j3; case _ q1 q2 q3 q4 q5 =>
    cases v <;> simp at *; case _ c =>
    cases c <;> simp at *; subst h
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    have lem1 := λ i => (q2 i).closed_rep
    have lem2 := q3.closed_rep
    subst q1; simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at *
    intro σ; apply And.intro
    apply Vec.ext_get; intro i; rw [<-lem1 i σ]; grind
    grind
  case octor =>
    cases lem; case _ j1 j2 j3 j4 =>
    cases j3; case _ q1 q2 q3 q4 q5 =>
    cases v <;> simp at *; case _ c =>
    cases c <;> simp at *; subst h
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    have lem1 := λ i => (q2 i).closed_rep
    have lem2 := q3.closed_rep
    subst q1; simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at *
    intro σ; apply And.intro
    apply Vec.ext_get; intro i; rw [<-lem1 i σ]; grind
    grind
  case openm =>
    cases lem; case _ j1 j2 =>
    cases j1; case _ q1 q2 q3 q4 q5 =>
    cases v <;> simp at *; subst h
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    have lem1 := λ i => (q2 i).closed_rep
    have lem2 := q3.closed_rep
    subst q1; simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at *
    intro σ; apply And.intro
    apply Vec.ext_get; intro i; rw [<-lem1 i σ]; grind
    grind

theorem GlobalWf.closed_lookup_spine_type_ren {G : List Global} :
  ⊢ G ->
  lookup_spine_type v G x = some T ->
  ∀ (r : Ren Ty), T⟨r⟩ = T
:= by
  intro wf h r
  have lem := closed_lookup_spine_type wf h r.to
  rcases T with ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩; simp at *
  rcases lem with ⟨h1, h2⟩
  apply And.intro
  rw [Subst.apply_stable rfl]; simp; apply h1
  rw [Subst.apply_stable rfl]; simp; apply h2

-- theorem Ty.spine_subst_flip {σ : Subst Ty} {T : Ty} :
--   T[σ].spine = some (x, sp) ->
--   ∃ sp', T.spine = some (x, sp')
-- := sorry

theorem GlobalWf.subst_cancel_lookup_ctor? {T T' : Ty} {G : List Global} {σ : Subst Ty} :
  Ty.data? v G T = true ->
  ⊢ G ->
  (e : T' = T[σ]) ->
  lookup_ctor? G v x T' ->
  lookup_ctor? G v x T
:= by
  intro h wf e j
  simp [lookup_ctor?, Ty.data?] at *
  generalize zdef : T.spine = z at *
  cases z <;> simp at *; case _ z =>
  rcases z with ⟨z, sp⟩
  have lem := Ty.spine_subst σ zdef
  subst e; rw [lem] at j; simp at j
  simp; apply j

theorem GlobalWf.subst_cancel_lookup_ctor?_ren {T T' : Ty} {G : List Global} {r : Ren Ty} :
  Ty.data? v G T = true ->
  ⊢ G ->
  (e : T' = T⟨r⟩) ->
  lookup_ctor? G v x T' ->
  lookup_ctor? G v x T
:= by
  intro h wf e j
  simp [lookup_ctor?, Ty.data?] at *
  generalize zdef : T.spine = z at *
  cases z <;> simp at *; case _ z =>
  rcases z with ⟨z, sp⟩
  have lem := Ty.spine_ren r zdef
  subst e; rw [lem] at j; simp at j
  simp; apply j

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

theorem Ty.data?_closed (σ : Subst Ty) : Ty.data? v G T -> Ty.data? v G T[σ] := by
  unfold data?; intro h
  generalize zdef : T.spine = z at *
  cases z <;> simp at *; case _ z =>
  rcases z with ⟨z, R⟩
  have lem := Ty.spine_subst σ zdef
  rw [lem]; simp; simp at h; apply h

theorem Ty.data?_closed_ren (r : Ren Ty) : Ty.data? v G T -> Ty.data? v G T⟨r⟩ := by
  unfold data?; intro h
  generalize zdef : T.spine = z at *
  cases z <;> simp at *; case _ z =>
  rcases z with ⟨z, R⟩
  have lem := Ty.spine_ren r zdef
  rw [lem]; simp; simp at h; apply h

theorem Query.closed {σ : Subst Ty} (wf : ⊢ G)
  : {S : Vec Ty n} ->
    (∀ (i : Fin n), Ty.data? v G S[i]) ->
    (e : S' = S[σ]) ->
    Query G v q S' ->
    Query G v q S
| .nil, h, e, .nil => .nil
| .cons hd tl, h, e, .cons j1 j2 => by
  simp at e; rw [e.1] at j1
  have lem1 := h 0; simp at lem1
  replace h := λ (i : Fin _) => h i.succ
  have lem := Query.closed wf h e.2 j2
  apply VecTyping.cons _ lem
  apply GlobalWf.subst_cancel_lookup_ctor? lem1 wf rfl j1

theorem Query.closed_ren {r : Ren Ty} (wf : ⊢ G)
  : {S : Vec Ty n} ->
    (∀ (i : Fin n), Ty.data? v G S[i]) ->
    (e : S' = S⟨r⟩) ->
    Query G v q S' ->
    Query G v q S
| .nil, h, e, .nil => .nil
| .cons hd tl, h, e, .cons j1 j2 => by
  simp at e; rw [e.1] at j1
  have lem1 := h 0; simp at lem1
  replace h := λ (i : Fin _) => h i.succ
  have lem := Query.closed_ren wf h e.2 j2
  apply VecTyping.cons _ lem
  apply GlobalWf.subst_cancel_lookup_ctor?_ren lem1 wf rfl j1

theorem CoercionProject.closed_rep :
  CoercionProject G Δ n T A ->
  (∀ (σ : Subst Ty), T[σ.lift Δ.length] = T) ->
  ∀ (σ : Subst Ty), A[σ.lift Δ.length] = A
| fst_app j, h => by simp at h; simp [*]
| snd_app j, h => by simp at h; simp [*]
| fst_arrow j, h => by simp at h; simp [*]
| snd_arrow j, h => by simp at h; simp [*]

theorem PatternBinders.closed_rep :
  PatternBinders v G Δ m S p ζ ξ ->
  ∀ (σ : Subst Ty), p[σ.lift Δ.length] = p
| .zero => by cases p; simp
| .succ j1 j2 j3 j4 j5 j6 =>
  have j2' := λ i => (j2 i).closed_rep
  have j6' := j6.closed_rep
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
    intro σ; apply Vec.ext_get; intro i
    replace j2' := j2' i σ; rw [<-j2']
    grind

@[simp]
theorem Pattern.bind_zero : {p : Pattern 0} -> p.bind = 0
| .nil => by simp [Pattern.bind]

theorem PatternBinders.length : PatternBinders v G Δ m S p ζ ξ -> p.bind = ξ.length
| zero => by simp
| succ j1 j2 e1 e2 e3 j3 => by
  have lem := j3.length
  simp [Pattern.bind, e2]; grind

@[simp]
theorem Pattern.bind_type_zero : {p : Pattern 0} -> p.bind_type = 0
| .nil => by simp [Pattern.bind_type]

theorem PatternBinders.length_type : PatternBinders v G Δ m S p ζ ξ -> p.bind_type = ζ.length
| zero => by simp
| succ j1 j2 e1 e2 e3 j3 => by
  have lem := j3.length_type
  simp [Pattern.bind_type]; grind

theorem Typing.closed_type_rep (wf : ⊢ G) :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[σ.lift Δ.length] = t ∧ A[σ.lift Δ.length] = A
| var j1 j2 =>
  have j2' := j2.closed_rep
  by simp; intro σ; simp at j2'; apply j2'
| defn j1 j2 =>
  have j2' := j2.closed_rep
  by simp; simp at j2'; intro σ; apply j2'
| spctor (As := As) (Bs := Bs) j1 e1 e2 j2 j3 j4 h1 h2 h3 =>
  have j1' := GlobalWf.closed_lookup_spine_type wf j1
  have j2' := λ i => (j2 i).closed_rep
  have j3' := λ i => (j3 i).closed_rep
  have j4' := λ i => (j4 i).closed_type_rep wf
  by
    intro σ
    have lem1 : As[σ.lift Δ.length] = As := by
      apply Vec.ext_get; intro i; rw [<-(j2' i σ)]; grind
    have lem2 : Bs[σ.lift Δ.length] = Bs := by
      apply Vec.ext_get; intro i; rw [<-(j3' i σ)]; grind
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    apply And.intro; apply And.intro
    apply lem1; apply And.intro; apply lem2
    funext; case _ i => apply (j4' i σ).1
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j1'
    simp [e2, -Subst.rewrite_lift_k, -Subst.rewrite_lift]
    conv =>
      rhs
      rw [<-(j1' (σ.lift Δ.length)).2]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    rw [Subst.compose_left_cons_lift_indirect (h := by simp; omega)]
    rw [lem1, lem2]; simp
| mtch (ζ := ζ) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).closed_type_rep wf
  have j3' := λ i => (j3 i).closed_rep
  have j4' := λ i => (j4 i).closed_type_rep wf
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    intro σ; apply And.intro; apply And.intro
    funext; case _ i => apply (j1' i σ).1
    apply And.intro
    funext; case _ i => apply j3'
    funext; case _ i =>
      have lem := (j3 i).length_type
      rw [lem, <-Subst.lift_of_add, Nat.add_comm]
      rw [<-List.length_append, (j4' i σ).1]
    have lem := (j4' 0 σ).2
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at lem
    rw [Nat.add_comm (n := (ζ 0).length)] at lem
    rw [Subst.lift_of_add] at lem
    rw [<-Subst.compose_commute_add_ren_subst] at lem
    have lem2 : A[σ.lift Δ.length ∘ Ren.add Ty (ζ 0).length]⟨Ren.sub Ty (ζ 0).length⟩
        = A⟨Ren.add Ty (ζ 0).length⟩⟨Ren.sub Ty (ζ 0).length⟩
      := by rw [<-lem]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at lem2
    apply lem2
| lam j1 j2 =>
  have j1' := j1.closed_rep
  have j2' := j2.closed_type_rep wf
  by {
    simp; simp at j1' j2'; intro σ
    exact ⟨⟨j1' σ, (j2' σ).1⟩, j1' σ, (j2' σ).2⟩
  }
| app j1 j2 =>
  have j1' := j1.closed_type_rep wf
  have j2' := j2.closed_type_rep wf
  by {
    simp; simp at j1' j2'; intro σ
    exact ⟨⟨(j1' σ).1, (j2' σ).1⟩, (j1' σ).2.2⟩
  }
| lamt j1 j2 =>
  have j2' := j2.closed_type_rep wf
  by simp; simp at j2'; apply j2'
| appt (P := P) (a := a) j1 j2 e =>
  have j1' := j1.closed_type_rep wf
  have j2' := j2.closed_rep
  by {
    simp [e, -Subst.rewrite_lift_k, -Subst.rewrite_lift]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j1' j2'
    intro σ; apply And.intro; exact ⟨j2' σ, (j1' σ).1⟩
    conv =>
      rhs
      rw [<-(j1' σ).2]
    simp [-Subst.rewrite_lift_k]; rw [j2' σ]
    rw [Subst.compose_ren_right_assoc]; simp
  }
| refl j =>
  have j' := j.closed_rep
  by simp; simp at j'; apply j'
| cast j1 j2 j3 e =>
  have j1' := j1.closed_rep
  have j2' := j2.closed_type_rep wf
  have j3' := j3.closed_type_rep wf
  by {
    simp [e, -Subst.rewrite_lift_k, -Subst.rewrite_lift]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j1' j2' j3'
    intro σ; apply And.intro; apply And.intro
    rw [<-Subst.rewrite_lift_succ]; apply j1' σ; apply And.intro
    apply (j2' σ).1; apply (j3' σ).1
    conv =>
      rhs
      rw [<-(j1' σ)]
    rw [Subst.rewrite_lift_succ]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
    rw [(j2' σ).2.2]; simp [-Subst.rewrite_lift_k]
    rw [Subst.compose_ren_right_assoc]; simp
  }
| prj j1 j2 =>
  have j1' := j1.closed_type_rep wf
  have j2' := j2.closed_rep (λ σ => (j1' σ).2)
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| allc j =>
  have j' := j.closed_type_rep wf
  by simp; simp at j'; apply j'
| apptc j1 j2 e1 e2 =>
  have j1' := j1.closed_type_rep wf
  have j2' := j2.closed_type_rep wf
  by {
    simp [e1, e2, -Subst.rewrite_lift_k, -Subst.rewrite_lift]
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j1' j2'
    intro σ; apply And.intro; exact ⟨(j1' σ).1, (j2' σ).1⟩
    apply And.intro
    conv =>
      rhs
      rw [<-(j1' σ).2.1]
    simp [-Subst.rewrite_lift_k]; rw [(j2' σ).2.1]
    rw [Subst.compose_ren_right_assoc]; simp
    conv =>
      rhs
      rw [<-(j1' σ).2.2]
    simp [-Subst.rewrite_lift_k]; rw [(j2' σ).2.2]
    rw [Subst.compose_ren_right_assoc]; simp
  }

theorem Typing.closed_type (wf : ⊢ G) :
  G&[],Γ ⊢ t : A ->
  ∀ (σ : Subst Ty), t[σ] = t ∧ A[σ] = A
:= by
  intro j σ
  have lem := closed_type_rep wf j σ; simp at lem
  exact lem

theorem Typing.closed_rep :
  G&Δ,Γ ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[σ.lift Γ.length ◾ τ] = t
| var (x := x) j1 j2 => by
  have lem : x < Γ.length := Γ.indexing_length_some j1
  simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift]
  intro σ τ; rw [subst_lift σ lem]; simp
| defn j1 j2 => by simp
| spctor j1 e1 e2 j2 j3 j4 h1 h2 h3 =>
  have j4' := λ i => (j4 i).closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| mtch (ξ := ξ) (ps := ps) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).closed_rep
  have j4' := λ i => (j4 i).closed_rep
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j4'
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
    intro σ τ; funext; case _ i =>
    have lem : (ps i).bind = (ξ i).length := (j3 i).length
    rw [lem, <-Subst.lift_of_add, Nat.add_comm]
    apply j4'
| lam j1 j2 =>
  have j2' := j2.closed_rep
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j2'
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
    intro σ τ; replace j2' := j2' σ τ
    rw [Subst.rewrite_lift_succ] at j2'; exact j2'
| app j1 j2 =>
  have j1' := j1.closed_rep
  have j2' := j2.closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| lamt j1 j2 =>
  have j2' := j2.closed_rep
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift] at j2'
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| appt j1 j2 e =>
  have j1' := j1.closed_rep
  have j2' := j2.closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| refl j => by simp
| cast j1 j2 j3 e =>
  have j2' := j2.closed_rep
  have j3' := j3.closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| prj j1 j2 =>
  have j1' := j1.closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| allc j =>
  have j' := j.closed_rep
  by
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *] at j'
    simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]
| apptc j1 j2 e1 e2 =>
  have j1' := j1.closed_rep
  have j2' := j2.closed_rep
  by simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift, *]

theorem Typing.closed :
  G&Δ,[] ⊢ t : A ->
  ∀ (σ : Subst Term) (τ : Subst Ty), t[σ ◾ τ] = t
:= by
  intro j σ
  have lem := closed_rep j σ; simp at lem
  exact lem

theorem CoercionProject.extend Δ
  : CoercionProject G Δ₁ n T A -> CoercionProject G (Δ₁ ++ Δ) n T A
| fst_app j => fst_app j.extend
| snd_app j => snd_app j.extend
| fst_arrow j => fst_arrow j.extend
| snd_arrow j => snd_arrow j.extend

theorem PatternBinders.extend Δ
  : PatternBinders v G Δ₁ m S p ζ ξ -> PatternBinders v G (Δ₁ ++ Δ) m S p ζ ξ
| zero => zero
| succ j1 j2 e1 e2 e3 j3 => succ j1 (λ i => (j2 i).extend) e1 e2 e3 (j3.extend _)

theorem Typing.extend Δ Γ : G&Δ₁,Γ₁ ⊢ t : A -> G&(Δ₁ ++ Δ),(Γ₁ ++ Γ) ⊢ t : A
| var (x := x) j1 j2 => var (extend_lemma j1) j2.extend
| defn j1 j2 => defn j1 j2.extend
| spctor j1 e1 e2 j2 j3 j4 j5 j6 j7 =>
  have j2' := λ i => (j2 i).extend (Δ₂ := Δ)
  have j3' := λ i => (j3 i).extend (Δ₂ := Δ)
  have j4' := λ i => (j4 i).extend Δ Γ
  spctor j1 e1 e2 j2' j3' j4' j5 j6 j7
| mtch (ζ := ζ) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).extend Δ Γ
  have j3' := λ i => (j3 i).extend Δ
  have j4' := λ i => (j4 i).extend Δ Γ⟨Ren.add Ty (ζ i).length⟩
  mtch j1' j2 j3' (j4' |> _root_.cast (by simp)) j5
| lam (A := A) j1 j2 => lam j1.extend (j2.extend _ _)
| app j1 j2 => app (j1.extend _ _) (j2.extend _ _)
| lamt j1 j2 => lamt j1.extend (j2.extend Δ Γ⟨.succ Ty⟩ ▸ simp)
| appt (P := P) j1 j2 e => appt (j1.extend _ _) j2.extend e
| refl j1 => refl j1.extend
| cast j1 j2 j3 e => cast j1.extend (j2.extend _ _) (j3.extend _ _) e
| prj j1 j2 => prj (j1.extend _ _) (j2.extend _)
| allc j1 => allc (j1.extend Δ Γ⟨.succ Ty⟩ ▸ simp)
| apptc j1 j2 e1 e2 => apptc (j1.extend _ _) (j2.extend _ _) e1 e2

theorem Typing.weaken_type_closed Δ :
  ⊢ G ->
  G&[],[] ⊢ t : A ->
  G&Δ,[] ⊢ t : A
:= by
  intro wf j
  have lem := Typing.extend Δ [] j
  simp at lem; apply lem

theorem Typing.weaken_closed Γ :
  ⊢ G ->
  G&Δ,[] ⊢ t : A ->
  G&Δ,Γ ⊢ t : A
:= by
  intro wf j
  have lem := Typing.extend [] Γ j
  simp at lem; apply lem

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
  have lem1 := Kinding.closed j1
  have lem2 := Typing.closed_type wf j2
  have lem3 := Typing.closed j2
  apply And.intro _; apply And.intro
  intro σ
  have lem4 := lem3 σ (Subst.id Ty); simp at lem4; apply lem4
  intro σ; apply (lem2 σ).1
  apply lem1

theorem GlobalWf.closed_lookup_defn_ren {G : List Global} :
  ⊢ G ->
  lookup_defn G x = some (A, t) ->
  (∀ (r : Ren Ty), A⟨r⟩ = A) ∧ (∀ (r : Ren Term), t⟨r⟩ = t) ∧ (∀ (r : Ren Ty), t⟨r⟩ = t)
:= by
  intro wf h
  unfold lookup_defn at h; simp at h
  replace h := Option.bind_eq_some_iff.1 h
  rcases h with ⟨e, h⟩
  cases e <;> simp at h; case _ z B s =>
  rcases h with ⟨h, e1, e2⟩; subst e1 e2
  have lem := EntryWf.from_lookup wf h
  cases lem; case _ j1 j2 lem =>
  have lem1 := Kinding.closed j1
  have lem2 := Typing.closed_type wf j2
  have lem3 := Typing.closed j2
  apply And.intro _; apply And.intro
  intro r
  have lem4 := lem3 r.to (Subst.id Ty); simp at lem4
  rw [Subst.apply_stable rfl]; apply lem4
  intro r; rw [Subst.apply_stable rfl]; apply (lem2 r.to).1
  intro r; rw [Subst.apply_stable rfl]; apply lem1

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
