import LeanSubst
import Core.Typing
import Core.Util
import Core.Metatheory.Rename

open Lilac
open LeanSubst

namespace Core

theorem Kinding.subst_lift {Δ Δσ : List Kind} {σ : Subst Ty} T :
  (∀ (i : Nat) K, Δ[i]? = some K -> G&Δσ ⊢ σ.act i : K) ->
  ∀ (i : Nat) K, (T::Δ)[i]? = some K -> G&(T::Δσ) ⊢ σ.lift.act i : K
:= by
  intro h1 i K h2
  cases i <;> simp at *
  case _ => subst h2; apply var; simp
  case _ i =>
    replace h1 := h1 i K h2
    replace h1 := Kinding.weaken T h1
    simp at h1; exact h1

theorem Kinding.subst Δσ (σ : Subst Ty) :
  (∀ (i : Nat) K, Δ[i]? = some K -> G&Δσ ⊢ σ.act i : K) ->
  G&Δ ⊢ A : K ->
  G&Δσ ⊢ A[σ] : K
:= by
  intro h j
  induction j generalizing Δσ σ <;> simp
  case var Δ x K j => apply h x K j
  case global j => apply global j
  case arrow j1 j2 ih1 ih2 =>
    apply arrow
    apply ih1 _ _ h
    apply ih2 _ _ h
  case all K Δ P j ih =>
    replace ih := ih (K :: Δσ) σ.lift (subst_lift K h)
    simp at ih
    apply all ih
  case app j1 j2 ih1 ih2 =>
    apply app
    apply ih1 _ _ h
    apply ih2 _ _ h
  case eq j1 j2 ih1 ih2 =>
    apply eq
    apply ih1 _ _ h
    apply ih2 _ _ h

theorem Kinding.beta :
  G&(T::Δ) ⊢ A : K ->
  G&Δ ⊢ t : T ->
  G&Δ ⊢ A[su t::+0σ] : K
:= by
  intro j1 j2
  apply Kinding.subst Δ (su t::+0σ) _ j1
  intro i K h; cases i <;> simp at *
  case _ => subst h; exact j2
  case _ i => apply var h

@[simp]
theorem Subst.compose_cons_lift
  [RenMap S S] [SubstMap S S] [SubstMapRenComposeLeft S S]
  {σ τ : Subst S} : σ.lift ∘ (x :: τ) = x :: σ ∘ τ
:= by
  simp [Subst.compose, Subst.cons]; funext; case _ i =>
  cases i <;> simp; case _ i =>
  generalize zdef : σ.act i = z
  cases z <;> simp [Subst.compose_ren_left]
  congr

theorem Subst.compose_append_id_commute_indirect
  [RenMap S S] [RenMapId S S] [RenMapCompose S S]
  [SubstMap S S] [SubstMapId S S] [SubstMapRenComposeLeft S S]
  {ℓ : List $ Action S} {σ : Subst S} (h : k = ℓ.length)
  : (ℓ ++ Subst.id S) ∘ σ = σ.lift k ∘ (ℓ[σ] ++ Subst.id S)
:= by
  induction ℓ generalizing σ k; simp [*]
  case _ hd tl ih =>
    simp [-Subst.rewrite_lift_k_ren] at *
    rw [@ih (k - 1) σ (by simp [*])]
    cases k; simp at h; case _ k =>
    simp [-Subst.rewrite_lift_k_ren]
    rw [Subst.rewrite_lift_succ, Subst.compose_cons_lift]

theorem Subst.compose_append_id_commute_direct
  [RenMap S S] [RenMapId S S] [RenMapCompose S S]
  [SubstMap S S] [SubstMapId S S] [SubstMapRenComposeLeft S S]
  {ℓ : List $ Action S} {σ : Subst S}
  : (ℓ ++ Subst.id S) ∘ σ = σ.lift ℓ.length ∘ (ℓ[σ] ++ Subst.id S)
:= by
  rw [compose_append_id_commute_indirect rfl]

theorem Typing.subst_type_lift {Δ Δσ : List Kind} {σ : Subst Ty} K :
  (∀ (i : Nat) T, Δ[i]? = some T → G&Δσ ⊢ (σ.act i) : T) ->
  (∀ (i : Nat) T, (K::Δ)[i]? = some T → G&(K::Δσ) ⊢ (σ.lift.act i) : T)
:= by
  intro h1 i T h2
  cases i <;> simp
  case _ => simp at h2; subst h2; apply Kinding.var; simp
  case _ i =>
    simp at h2
    have h3 := h1 _ _ h2
    have lem := Kinding.rename (K::Δσ) (Ren.succ Ty) (by simp) h3
    simp at lem; apply lem

theorem Typing.subst_type_lift_k {Δ Δσ : List Kind} {σ : Subst Ty} K :
  (∀ (i : Nat) T, Δ[i]? = some T → G&Δσ ⊢ (σ.act i) : T) ->
  (∀ (i : Nat) T, (K ++ Δ)[i]? = some T → G&(K ++ Δσ) ⊢ ((σ.lift K.length).act i) : T)
:= by
  intro h1 i T h2
  induction K generalizing i T
  case _ =>
    simp at *
    apply h1 _ _ h2
  case _ hd tl ih =>
    cases i <;> simp [-Subst.rewrite_lift_k, *]
    case _ =>
      simp at h2; subst h2
      apply Kinding.var; simp
    case _ i =>
      rw [Subst.rewrite_lift_succ, Subst.rewrite_lift]
      simp [-Subst.rewrite_lift_k]
      simp at h2
      have lem := ih _ _ h2
      have lem2 := Kinding.rename (hd::(tl ++ Δσ)) (Ren.succ Ty) (by simp) lem
      simp [-Subst.rewrite_lift_k] at lem2
      apply lem2

theorem CoercionProject.subst_type Δσ (σ : Subst Ty)
  (h : (∀ (i : Nat) K, Δ[i]? = some K -> G&Δσ ⊢ σ.act i : K))
  : CoercionProject G Δ n T A -> CoercionProject G Δσ n T[σ] A[σ]
| fst_app j => fst_app (j.subst _ _ h)
| snd_app j => snd_app (j.subst _ _ h)
| fst_arrow j => fst_arrow (j.subst _ _ h)
| snd_arrow j => snd_arrow (j.subst _ _ h)

theorem Query.Match.subst_type (σ : Subst Ty) :
  Query.Match q p -> Query.Match q p[σ]
| .nil => .nil
| .cons ⟨na, As, nb, e⟩ j2 =>
  let j2' := Query.Match.subst_type σ j2
  .cons ⟨na, As[σ], nb, by grind⟩ j2'

theorem PatternBinders.subst_type Δσ (σ : Subst Ty) (wf : ⊢ G)
  (h : (∀ (i : Nat) K, Δ[i]? = some K -> G&Δσ ⊢ σ.act i : K))
  : PatternBinders v G Δ m S p ζ ξ ->
  PatternBinders v G Δσ m S[σ] p[σ] ζ ξ[σ.lift ζ.length]
| zero => zero
| @succ v G Δ nc c na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' e1 j1 e2 e3 e4 j2 =>
  have e1' : lookup_spine_type (.data v) G c = (some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩)[σ] := by
    have lem := GlobalWf.closed_lookup_spine_type wf e1 σ
    simp; simp at lem; grind
  have j1' := λ i => (j1 i).subst Δσ σ h
  have j2' := j2.subst_type Δσ σ wf h
  have e2' : Ts'[σ.lift (nb + ℓ1.length)] = (Vec.map (fun (x:Ty) => x[σ.lift (na + nb)]) Ts)[(List.map su As[σ].list.reverse ++ Subst.id Ty).lift nb]⟨Ren.add Ty ℓ1.length⟩ := by
    rw [e2, Vec.smap_promote]; simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]; congr 1
    rw [Subst.compose_ren_right_assoc]
    rw [Subst.lift_of_add, <-Subst.compose_commute_add_ren_subst]
    rw [<-Subst.compose_ren_right_assoc2, <-Subst.rewrite_lift_compose, Subst.compose_append_id_commute_direct]
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    rw [Subst.lift_of_add]
  have e3' : ℓ2'[σ.lift (nb + ℓ1.length)] = ℓ2[σ.lift ℓ1.length]⟨(Ren.add Ty nb).lift ℓ1.length⟩ := by
    rw [e3]; simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    rw [Subst.lift_of_add, <-Subst.rewrite_lift_compose_ren_left, <-Subst.compose_commute_add_ren_subst]
    rw [<-Subst.lift_compose_ren_right]
  have e4' : R'[σ]⟨.add Ty nb⟩ = R[σ.lift (na + nb)][(List.map su As[σ].list.reverse ++ Subst.id Ty).lift nb] := by
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    rw [Subst.compose_commute_add_ren_subst, <-Subst.apply_ren_compose_left, e4]
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    rw [<-Subst.rewrite_lift_compose]
    rw [Subst.lift_of_add, <-Subst.rewrite_lift_compose]; congr 2
    rw [Subst.compose_append_id_commute_indirect (k := na) (by simp)]; simp
  succ (Ts' := Ts'[σ.lift (nb + ℓ1.length)]) (ℓ2' := ℓ2'[σ.lift (nb + ℓ1.length)])
    e1' (j1' ▸ simp) e2' e3' e4' j2' ▸ congr; simp; grind

theorem Typing.subst_type Δσ (σ : Subst Ty) (wf : ⊢ G)
  (h : (∀ (i : Nat) K, Δ[i]? = some K -> G&Δσ ⊢ σ.act i : K))
  : G&Δ,Γ ⊢ t : A -> G&Δσ,Γ[σ] ⊢ t[σ] : A[σ]
| var (x := x) j1 j2 =>
  have lem : Γ[x]?[σ] = (some A)[σ] := by rw [j1]
  var (by simp at lem; exact lem) (j2.subst _ _ h)
| defn (x := x) (t := t) j1 j2 =>
  have j1' : lookup_defn G x = some (A[σ], t[σ]) := by
    have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn wf j1
    rw [e1 σ, e3 σ]; exact j1
  defn j1' (j2.subst _ _ h)
| @spctor G Δ Γ m1 m2 n x v Ks1 Ks2 Ts Ts' R R' As Bs ts j1 e1 e2 j2 j3 j4 j5 j6 j7 =>
  have j1' : lookup_spine_type v G x = (some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩)[σ] := by
    have lem := GlobalWf.closed_lookup_spine_type wf j1 σ
    simp; simp at lem; grind
  have e1' : Ts'[σ] = Ts[σ.lift (m1 + m2)][List.map su (As[σ].list ++ Bs[σ].list).reverse ++ Subst.id Ty] := by
    rw [e1]; simp [-Subst.rewrite_lift_k];
    generalize ℓdef : (List.map su Bs.list).reverse ++ (List.map su As.list).reverse = ℓ
    have lem : (List.map su Bs[σ].list).reverse ++ (List.map su As[σ].list).reverse = ℓ[σ] := by
      rw [<-ℓdef]; simp
    rw [lem]
    generalize kdef : m1 + m2 = k
    rw [<-Subst.compose_append_id_commute_indirect]; simp
    rw [<-ℓdef]; simp; rw [<-kdef]; omega
  have e2' : R'[σ] = R[σ.lift (m1 + m2)][List.map su (As[σ].list ++ Bs[σ].list).reverse ++ Subst.id Ty] := by
    rw [e2]; simp [-Subst.rewrite_lift_k]
    generalize ℓdef : (List.map su Bs.list).reverse ++ (List.map su As.list).reverse = ℓ
    have lem : (List.map su Bs[σ].list).reverse ++ (List.map su As[σ].list).reverse = ℓ[σ] := by
      rw [<-ℓdef]; simp
    rw [lem]
    rw [<-Subst.compose_append_id_commute_indirect]; simp
    rw [<-ℓdef]; simp; omega
  have j2' : ∀ (i : Fin m1), G&Δσ ⊢ As[σ][i] : Ks1[i] := λ i =>
    let lem := (j2 i).subst Δσ σ h
    by simp at lem; exact lem
  have j3' : ∀ (i : Fin m2), G&Δσ ⊢ Bs[σ][i] : Ks2[i] := λ i =>
    let lem := (j3 i).subst Δσ σ h
    by simp at lem; exact lem
  have j4' : ∀ (i : Fin n), G&Δσ,Γ[σ] ⊢ (ts i)[σ] : Ts'[i][σ] := λ i =>
    let lem := (j4 i).subst_type Δσ σ wf h
    by simp at lem; simp; exact lem
  have j5' : ∀ c, v = .data c → lookup_ctor? G c x R[σ.lift (m1 + m2)] = true :=
    have lem := GlobalWf.closed_lookup_spine_type wf j1 σ
    by simp at lem; simp; rw [lem.2]; exact j5
  have j6' : ∀ (c : DataConst), v = .data c → ∀ (i : Nat), i < m1 → i + m2 ∈ R[σ.lift (m1 + m2)] := by
    intro c h1 i h2
    have lem := j6 c h1 i h2
    apply FV.smap_lift _ lem; grind
  have j7' : v = .openm → ∀ (i : Fin n), Ty.data? DataConst.opn G Ts[σ.lift (m1 + m2)][i] := λ e i =>
    Ty.data?_closed (σ.lift (m1 + m2)) (j7 e i) ▸ simp
  spctor (Ts := Ts[σ.lift (m1 + m2)]) (R := R[σ.lift (m1 + m2)])
    (j1' ▸ simp) e1' e2' j2' j3' (λ i => j4' i ▸ simp [Term.Ty.smap_promote]) j5' j6' j7'
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ζ := ζ) (ξ := ξ) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).subst_type Δσ σ wf h
  have j2' := λ i => Ty.data?_closed σ (j2 i)
  let ξ' := λ (i : Fin n) => (ξ i)[σ.lift (ζ i).length]
  have j3' : ∀ (i : Fin n), PatternBinders .cls G Δσ m S.to[σ] (ps i)[σ] (ζ i) (ξ' i) :=
    λ i => (j3 i).subst_type Δσ σ wf h
  have j4' : ∀ (i : Fin n), G&(ζ i ++ Δσ),((ξ' i) ++ Γ[σ]⟨.add Ty (ζ i).length⟩) ⊢ (ts i)[σ.lift (ps i).bind_type] : A[σ]⟨.add Ty (ζ i).length⟩ := λ i => by
    have lem1 := subst_type_lift_k (ζ i) h
    have lem2 : (ζ i).length = (ps i).bind_type := Eq.symm (j3 i).length_type
    rw [lem2] at lem1
    have lem3 := (j4 i).subst_type (ζ i ++ Δσ) (σ.lift (ps i).bind_type) wf lem1
    rw [lem2] at lem3; simp [-Subst.rewrite_lift_k] at lem3
    rw [<-Subst.compose_commute_add_ren_subst] at lem3
    simp [-Subst.rewrite_lift_k, lem2, ξ']; exact lem3
  have j5' : ∀ {q}, (Query G .cls q S[σ]) → ∃ i, Query.Match q (ps i)[σ] :=
    λ q => match j5 (Query.closed wf rfl q) with
          | ⟨i, m⟩ => ⟨i, Query.Match.subst_type σ m⟩
  mtch (ζ := ζ) (ξ := ξ') j1' j2'
    (λ i => j3' i ▸ congr 1; grind)
    (λ i => (j4' i) ▸ congr 1)
    (λ {q} => @j5' q ▸ grind)
| lam j1 j2 => lam (j1.subst Δσ σ h) (j2.subst_type _ _ wf h)
| app j1 j2 => app (j1.subst_type _ _ wf h) (j2.subst_type _ _ wf h)
| lamt (K := K) (P := P) (t := t) j1 j2 =>
  let j2' : G&(K :: Δσ),Γ[σ]⟨.succ Ty⟩ ⊢ t[σ.lift] : P[σ.lift] := by
    have lem := j2.subst_type (K::Δσ) σ.lift wf (Typing.subst_type_lift K h)
    simp; simp at lem; exact lem
  lamt (j1.subst Δσ σ h) j2'
| appt (P := P) j1 j2 e =>
  appt (P := P[σ.lift]) (j1.subst_type Δσ σ wf h) (j2.subst Δσ σ h) (by simp [e, Subst.compose_ren_right_assoc])
| refl j1 => refl (j1.subst Δσ σ h)
| cast (K := K) (A := A) (R := R) (R' := R') (c := c) (t := t) j1 j2 j3 e =>
  have j1' := j1.subst _ _ (Kinding.subst_lift _ h)
  have j2' := j2.subst_type Δσ σ wf h
  have j3' : G&Δσ,Γ[σ] ⊢ t[σ] : R[σ.lift][su A[σ] :: +0σ] :=
    have lem := j3.subst_type Δσ σ wf h
    by simp [Subst.compose_ren_right_assoc]; simp at lem; exact lem
  have lem : G&Δσ,Γ[σ] ⊢ .cast R[σ.lift] c[σ] t[σ] : R'[σ] :=
    cast j1' j2' j3' (by simp [e, Ty.smap_promote, Subst.compose_ren_right_assoc])
  by simp; simp at lem; exact lem
| prj j1 j2 => prj (j1.subst_type _ _ wf h) (j2.subst_type _ _ h)
| allc (K := K) (A := A) (B := B) (t := t) j1 =>
  have j1' : G&(K::Δσ),Γ[σ]⟨.succ Ty⟩ ⊢ t[σ.lift] : (A[σ.lift] ~[★]~ B[σ.lift]) := by
    have lem := j1.subst_type (K::Δσ) σ.lift wf (Typing.subst_type_lift K h)
    simp; simp at lem; exact lem
  allc j1'
| apptc j1 j2 e1 e2 =>
  let j1' := j1.subst_type _ _ wf h
  let j2' := j2.subst_type _ _ wf h
  apptc j1' j2'
    (by simp [Ty.smap_promote, e1, Subst.compose_ren_right_assoc])
    (by simp [Ty.smap_promote, e2, Subst.compose_ren_right_assoc])

theorem Typing.beta_type :
  ⊢ G ->
  G&(K::Δ),Γ ⊢ t : A ->
  G&Δ ⊢ a : K ->
  G&Δ,Γ[su a::+0σ] ⊢ t[su a::+0σ] : A[su a::+0σ]
:= by
  intro wf j1 j2
  apply subst_type Δ (su a::+0σ) wf _ j1
  intro i T h
  cases i <;> simp at *
  case _ => subst h; exact j2
  case _ i => apply Kinding.var h

theorem Typing.subst_lift {Γ Γσ : List Ty} {σ : Subst Term} (wf : ⊢ G) T :
  (∀ (i:Nat) A, Γ[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γσ ⊢ σ.act i : A) ->
  ∀ (i:Nat) A, (T::Γ)[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,(T::Γσ) ⊢ σ.lift.act i : A
:= by
  intro h1 i A h2 h3
  cases i <;> simp at *
  case _ =>
    subst h2
    apply Typing.var; simp
    apply h3
  case _ i =>
    have h4 := h1 _ _ h2 h3
    replace h4 := Typing.rename (T::Γσ) (Ren.succ Term) wf (by simp) h4
    simp at h4; apply h4

theorem Typing.subst_lift_k {Γ Γσ : List Ty} {σ : Subst Term} (wf : ⊢ G) T :
  (∀ (i:Nat) A, Γ[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γσ ⊢ σ.act i : A) ->
  ∀ (i:Nat) A, (T ++ Γ)[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,(T ++ Γσ) ⊢ (σ.lift T.length).act i : A
:= by
  intro h1 i A h2 h3
  induction T generalizing i A <;> simp [-Subst.rewrite_lift_k] at *
  case _ => apply h1 _ _ h2 h3
  case _ hd tl ih =>
    cases i
    case _ =>
      simp at h2; subst h2
      simp; apply Typing.var; simp
      apply h3
    case _ i =>
      rw [Subst.rewrite_lift_succ, Subst.rewrite_lift]
      simp [-Subst.rewrite_lift_k] at *
      replace ih := ih _ _ h2 h3
      have lem := Typing.rename (hd::(tl ++ Γσ)) (Ren.succ Term) wf (by simp) ih
      simp [-Subst.rewrite_lift_k] at *
      apply lem

theorem Typing.subst_lift_succ {Γ Γσ : List Ty} {σ : Subst Term} (wf : ⊢ G) K :
  (∀ (i:Nat) A, Γ[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γσ ⊢ σ.act i : A) ->
  ∀ (i:Nat) A, Γ⟨.succ Ty⟩[i]? = some A -> G&(K::Δ) ⊢ A : ★ -> G&(K::Δ),Γσ⟨.succ Ty⟩ ⊢ ((σ ◾ Ren.succ Ty).act i) : A
:= by
  intro h1 i A h2 h3
  have lem : ∃ A', A = A'⟨Ren.succ Ty⟩ := by
    rw [<-List.getElem?_rmap] at h2
    generalize zdef : Γ[i]? = z
    cases z
    case _ => rw [zdef] at h2; simp at h2
    case _ z =>
      rw [zdef] at h2; simp at h2; subst h2
      exists z
  rcases lem with ⟨A', lem⟩; subst lem
  have h4 := Kinding.strong_rename (Δr := Δ) (Ren.pred Ty) h3 (by {
    intro x q; simp; cases x <;> simp
    exfalso; apply FV.zero_not_in_succ q
  }); simp at h4
  have lem2 : Γ⟨.succ Ty⟩[i]?⟨.pred Ty⟩ = (some A')⟨.succ Ty⟩⟨.pred Ty⟩ := by rw [h2]; simp
  simp at lem2
  have lem3 := h1 _ _ lem2 h4
  have lem4 := Typing.rename_type (K::Δ) (Ren.succ Ty) wf (by simp) lem3
  simp at lem4; simp [Subst.hcompose_ren]; apply lem4

theorem Typing.subst_lift_add {Γ Γσ : List Ty} {σ : Subst Term} (wf : ⊢ G) ζ :
  (∀ (i:Nat) A, Γ[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γσ ⊢ σ.act i : A) ->
  ∀ (i:Nat) A, Γ⟨.add Ty ζ.length⟩[i]? = some A -> G&(ζ ++ Δ) ⊢ A : ★ -> G&(ζ ++ Δ),Γσ⟨.add Ty ζ.length⟩ ⊢ ((σ ◾ Ren.add Ty ζ.length).act i) : A
:= by
  intro h1 i A h2 h3
  have lem : ∃ A', A = A'⟨Ren.add Ty ζ.length⟩ := by
    rw [<-List.getElem?_rmap] at h2
    generalize zdef : Γ[i]? = z
    cases z
    case _ => rw [zdef] at h2; simp at h2
    case _ z =>
      rw [zdef] at h2; simp at h2; subst h2
      exists z
  rcases lem with ⟨A', lem⟩; subst lem
  have h4 := Kinding.strong_rename (Δr := Δ) (Ren.sub Ty ζ.length) h3 (by {
    intro x q; simp
    have lem : x ≥ ζ.length := FV.mem_add q
    grind
  }); simp at h4
  have lem2 : Γ⟨.add Ty ζ.length⟩[i]?⟨.sub Ty ζ.length⟩ = (some A')⟨.add Ty ζ.length⟩⟨.sub Ty ζ.length⟩ := by rw [h2]; simp
  simp at lem2
  have lem3 := h1 _ _ lem2 h4
  have lem4 := Typing.rename_type (ζ ++ Δ) (Ren.add Ty ζ.length) wf (by simp; grind) lem3
  simp at lem4; simp [Subst.hcompose_ren]; apply lem4

theorem Typing.subst Γσ (σ : Subst Term) (wf : ⊢ G)
  (h : ∀ (i:Nat) A, Γ[i]? = some A -> G&Δ ⊢ A : ★ -> G&Δ,Γσ ⊢ σ.act i : A)
  : G&Δ,Γ ⊢ t : A ->
  G&Δ,Γσ ⊢ t[σ] : A
| var (x := x) j1 j2 => h x A j1 j2
| defn (x := x) (t := t) j1 j2 =>
  have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn wf j1
  have j1' : lookup_defn G x = some (A, t[σ]) := by
    rw [e2 σ]; exact j1
  defn j1' j2
| spctor j1 e1 e2 j2 j3 j4 j5 j6 j7 => spctor j1 e1 e2 j2 j3 (λ i => (j4 i).subst _ _ wf h) j5 j6 j7
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ζ := ζ) (ξ := ξ) j1 j2 j3 j4 j5 =>
  have j4' : ∀ (i : Fin n), G&(ζ i ++ Δ),(ξ i ++ Γσ⟨Ren.add Ty (ζ i).length⟩) ⊢ (ts i)[σ.lift (ps i).bind ◾ Subst.add Ty (ps i).bind_type] : A⟨Ren.add Ty (ζ i).length⟩ := λ i =>
    have lem0 : (ps i).bind_type = (ζ i).length := (j3 i).length_type
    have lem1 : (ps i).bind = (ξ i).length := (j3 i).length
    have lem2 (k:Nat) A :
      (ξ i ++ Γ⟨Ren.add Ty (ζ i).length⟩)[k]? = some A ->
      G&(ζ i ++ Δ) ⊢ A : ★ ->
      G&(ζ i ++ Δ),(ξ i ++ Γσ⟨Ren.add Ty (ζ i).length⟩) ⊢ ((σ.lift (ps i).bind ◾ Subst.add Ty (ps i).bind_type).act k) : A
    := by
      rw [lem1]
      have h2 := subst_lift_add wf (ζ i) h
      generalize zdef : σ ◾ Ren.add Ty (ζ i).length = z at h2
      have h3 := subst_lift_k wf (ξ i) h2 k A
      subst zdef; simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k] at h3
      rw [Subst.hcompose_action, lem0]
      have lem3 : smap (Subst.add Ty (ζ i).length) = rmap (S := Action Term) (Ren.add Ty (ζ i).length) := by
        funext; case _ a =>
        cases a <;> simp
        rw [Subst.apply_stable]; simp
      rw [lem3]; apply h3
    (j4 i).subst (ξ i ++ Γσ⟨Ren.add Ty (ζ i).length⟩) (σ.lift (ps i).bind ◾ Subst.add Ty (ps i).bind_type) wf lem2
  mtch (λ i => (j1 i).subst _ _ wf h) j2 j3 j4' j5
| lam (A := A) j1 j2 =>
  let j2' := (j2.subst (A::Γσ) σ.lift wf (Typing.subst_lift wf A h) ▸ simp [Term.smap_promote])
  lam j1 j2'
| app j1 j2 => app (j1.subst _ _ wf h) (j2.subst _ _ wf h)
| lamt j1 j2 =>
  lamt j1 (j2.subst _ _ wf (Typing.subst_lift_succ wf _ h))
| appt (P := P) j1 j2 e => appt (j1.subst _ _ wf h) j2 (by simp [*])
| refl j1 => refl j1
| cast j1 j2 j3 e => cast j1 (j2.subst _ _ wf h) (j3.subst _ _ wf h) e
| prj j1 j2 => prj (j1.subst _ _ wf h) j2
| allc j1 =>
  allc (j1.subst _ _ wf (Typing.subst_lift_succ wf _ h))
| apptc j1 j2 e1 e2 => apptc (j1.subst _ _ wf h) (j2.subst _ _ wf h) e1 e2

theorem Typing.beta :
  ⊢ G ->
  G&Δ,(A::Γ) ⊢ t : T ->
  G&Δ,Γ ⊢ a : A ->
  G&Δ,Γ ⊢ t[su a::+0σ] : T
:= by
  intro wf j1 j2
  apply subst Γ (su a::+0σ) wf _ j1
  intro i B e h
  cases i <;> simp at *
  case _ => subst e; exact j2
  case _ i => apply var e h
end Core
