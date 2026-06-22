
import Core.Typing
import Core.Util
import Core.Metatheory.FreeVars
import Core.Metatheory.Closed

open Lilac
open LeanSubst

namespace Core



-- theorem GlobalWf.closed_ctors {v : Fun.Vec (Option Entry) n} {d : Option Entry} :
--   ((Option.map Entry.type d).get! = some T -> ∀ σ, T[σ] = T) ->
--   (∀ i e, v i = some e -> e.type = some T -> ∀ σ, T[σ] = T) ->
--   (Option.map Entry.type (Vec.fold d Option.or v.to)).get! = some T ->
--   ∀ σ, T[σ] = T
-- := by
--   sorry
  -- intro h1 h2 h3
  -- induction v using Vec.induction
  -- case nil => apply h1 h3
  -- case cons hd tl ih =>
  --   simp at h3
  --   cases hd <;> simp at *
  --   case none =>
  --     apply ih _
  --     apply h3
  --     intro i en e1 e2
  --     replace h2 := h2 (Fin.succ i) en (by simp; exact e1) e2
  --     apply h2
  --   case some =>
  --     apply h2 0 _ _ h3; simp

-- theorem GlobalWf.closed {G : List Global} :
--   ⊢ G ->
--   lookup_type G x = some T ->
--   ∀ σ, T[σ] = T
-- := by
--   sorry
  -- intro j h
  -- unfold lookup_type at h
  -- fun_induction lookup
  -- all_goals try solve | simp [Entry.type] at h
  -- all_goals try solve | case _ ih => apply ih (tail j) h
  -- case _ n y K cs1 tl cs2 e ih =>
  --   have lem := head j
  --   cases lem; case _ ctors =>
  --   apply closed_ctors (ih (tail j)) _ h
  --   intro i e q1 q2
  --   subst cs2; simp at q1; rcases q1 with ⟨e1, e2⟩
  --   generalize zdef : cs1 i = z at *
  --   rcases z with ⟨y, T'⟩; simp at *; subst e1 e2
  --   simp [Entry.type] at q2; subst q2
  --   replace ctors := ctors i x T' (by rw [zdef])
  --   apply Kinding.closed ctors.1
  -- case _ y T tl e =>
  --   replace e := LawfulBEq.eq_of_beq e
  --   simp [Entry.type] at h; subst e h
  --   have lem := head j
  --   cases lem ; case _ j =>
  --   apply Kinding.closed j
  -- case _ y T b tl e =>
  --   replace e := LawfulBEq.eq_of_beq e
  --   simp [Entry.type] at h; subst e h
  --   have lem := head j
  --   cases lem; case _ j1 j2 =>
  --   apply Kinding.closed j1
  -- case _ y T tl e =>
  --   replace e := LawfulBEq.eq_of_beq e
  --   simp [Entry.type] at h; subst e h
  --   cases j; case _ wf j =>
  --   cases j; case _ j =>
  --   have lemj : ∃ b, (tl&[] ⊢ T : .base b) := by
  --     apply ValidInstTy.closed j
  --   cases lemj; case _ lemj =>
  --   apply Kinding.closed lemj

theorem Kinding.strong_rename_lift {T : Ty} {Δr Δ : List Kind} {r : Ren Ty} K :
  (∀ x, x + 1 ∈ T -> Δr[r.act x]? = Δ[x]?) ->
  ∀ x, x ∈ T -> (K::Δr)[r.lift.act x]? = (K ::Δ)[x]? := by
intro h1 x h2
induction x
case _ => simp [Ren.lift] at *
case succ n ih =>
  replace h1 := h1 n h2
  simp [Ren.lift]; assumption

theorem Kinding.strong_rename {Δ Δr : List Kind} {T : Ty} (r : Ren Ty)  :
  G&Δ ⊢ T : K ->
  (∀ x : Nat,  x ∈ T -> Δr[r.act x]? = Δ[x]?) ->
  G&Δr ⊢ T⟨r⟩ : K := by
intro j h
induction j generalizing Δr r <;> simp [-Subst.rewrite_lift_k] at *
case var x K j =>
  replace h := h x (by apply Ty.FV.var)
  apply Kinding.var
  rw[<-j]; assumption
case global => apply Kinding.global; assumption
case arrow A B j1 j2 ih1 ih2 =>
  apply Kinding.arrow
  apply ih1
  · intro i h
    replace h : i ∈ (A -:> B) := by apply Ty.FV.arrowr; assumption
    revert i; apply h
  apply ih2
  · intro i h1
    replace h1 : i ∈ (A -:> B) := by apply Ty.FV.arrowl; assumption
    revert i; apply h
case eq A K B _ _ ih1 ih2 =>
  apply Kinding.eq
  apply ih1
  · intro i h
    replace h : i ∈ (A ~[K]~ B) := by apply Ty.FV.eqr; assumption
    revert i; apply h
  apply ih2
  · intro i h1
    replace h1 : i ∈ (A ~[K]~ B) := by apply Ty.FV.eql; assumption
    revert i; apply h
case app A _ _ B _ _ ih1 ih2 =>
  apply Kinding.app
  apply ih1
  · intro i h
    replace h : i ∈ (A • B) := by apply Ty.FV.appr; assumption
    revert i; apply h
  apply ih2
  · intro i h1
    replace h1 : i ∈ (A • B) := by apply Ty.FV.appl; assumption
    revert i; apply h
case all K Δ P _ ih =>
  have lem : ∀ (x : Nat), x + 1 ∈ P → (Δr)[r.act x]? = Δ[x]? := by
    intro i x
    replace x := Ty.FV.all (K := K) x
    replace h := @h i x; simp at h; assumption
  replace lem := Kinding.strong_rename_lift K lem
  apply Kinding.all
  replace ih := @ih (K :: Δr) r.lift
  simp [-Subst.rewrite_lift_k] at ih; grind

theorem Kinding.rename_lift {Δ Δr : List Kind} K (r : Ren Ty) :
  (∀ i, Δ[i]? = Δr[r.act i]?) ->
  ∀ i, (K::Δ)[i]? = (K::Δr)[r.lift.act i]?
:= by
  intro h i
  cases i <;> simp [Ren.lift] at *
  case _ i => exact h i

theorem Kinding.rename Δr (r : Ren Ty) :
  (∀ i, Δ[i]? = Δr[r.act i]?) ->
  G&Δ ⊢ A : K ->
  G&Δr ⊢ A⟨r⟩ : K
:= by
  intro h j
  apply Kinding.strong_rename _ j
  intro x _ ; replace h := @h x; symm at h; assumption

theorem Kinding.weaken T : G&Δ ⊢ A : K -> G&(T::Δ) ⊢ A⟨.succ Ty⟩ : K := by
  intro j; apply rename (T::Δ) (.succ Ty) _ j
  intro i; cases i <;> simp

theorem Typing.rename_rename {Γ Γr : List Ty} (r1 : Ren Term) (r2 : Ren Ty) :
  (∀ {i}, Γ[i]? = Γr[r1.act i]?) ->
  (∀ {i}, Γ[i]?⟨r2⟩ = Γr[r1.act i]?⟨r2⟩)
:= by intro h i; rw [h]

theorem Typing.rename_lift {Γ Γr : List Ty} (r : Ren Term) T :
  (∀ {i}, Γ[i]? = Γr[r.act i]?) ->
  ∀ {i}, (T::Γ)[i]? = (T::Γr)[r.lift.act i]?
:= by
  intro h1 i
  cases i <;> simp [Ren.lift] at *
  case _ => exact h1

theorem Typing.rename_lift_k {Γ Γr : List Ty} (r : Ren Term) T :
  (∀ {i}, Γ[i]? = Γr[r.act i]?) ->
  ∀ {i}, (T ++ Γ)[i]? = (T ++ Γr)[(r.lift T.length).act i]?
:= by
  intro h1 i
  induction T generalizing Γ i <;> simp [-Subst.rewrite_lift_k_ren]
  case nil => rw [h1]
  case cons hd tl ih =>
    cases i <;> simp [-Subst.rewrite_lift_k_ren, *]
    case _ i =>
      rw [Ren.lift_of_succ, Subst.rewrite_lift_ren]
      simp [-Subst.rewrite_lift_k_ren]

theorem Typing.rename_type_lift {Δ Δr : List Kind} {r : Ren Ty} K :
  (∀ (i : Nat), Δ[i]? = Δr[r.act i]?) ->
  ∀ (i : Nat), (K :: Δ)[i]? = (K :: Δr)[r.lift.act i]?
:= by
  intro h i
  cases i <;> simp [Ren.lift]
  apply h _

theorem Typing.rename_type_lift_k {Δ Δr : List Kind} {r : Ren Ty} K :
  (∀ (i : Nat), Δ[i]? = Δr[r.act i]?) ->
  ∀ (i : Nat), (K ++ Δ)[i]? = (K ++ Δr)[(r.lift K.length).act i]?
:= by
  intro h i
  induction K generalizing Δ i <;> simp [-Subst.rewrite_lift_k_ren]
  case nil => rw [h i]
  case cons hd tl ih =>
    cases i <;> simp [-Subst.rewrite_lift_k_ren, *]
    case _ i =>
      rw [Ren.lift_of_succ, Subst.rewrite_lift_ren]
      simp [-Subst.rewrite_lift_k_ren]

theorem CoercionProject.rename_type Δr (r : Ren Ty) (h : ∀ i, Δ[i]? = Δr[r.act i]?)
  : CoercionProject G Δ n T A -> CoercionProject G Δr n T⟨r⟩ A⟨r⟩
| fst_app j => fst_app (j.rename _ _ h)
| snd_app j => snd_app (j.rename _ _ h)
| fst_arrow j => fst_arrow (j.rename _ _ h)
| snd_arrow j => snd_arrow (j.rename _ _ h)

theorem Ren.compose_cons_id_commute {x : Nat} {r : Ren S} : (x :: Ren.id S) ∘ r = r.lift ∘ (r.act x :: Ren.id S) := by
  simp [Ren.compose]; funext; case _ i =>
  cases i <;> simp

theorem Ren.compose_append_id_commute {ℓ : List Nat} {r : Ren S} : (ℓ ++ Ren.id S) ∘ r = r.lift ℓ.length ∘ (ℓ⟨r⟩ ++ Ren.id S) := by
  induction ℓ generalizing r; simp
  case _ hd tl ih =>
  simp [-Subst.rewrite_lift_k_ren]
  rw [Ren.lift_of_succ]; simp [-Subst.rewrite_lift_k_ren] at *
  rw [ih]; congr

@[simp]
theorem Subst.compose_ren_right_cons [RenMap S S] {x : Action S} {σ : Subst S} {r : Ren S} : (x :: σ) ∘ r = x⟨r⟩ :: σ ∘ r := by
  simp [Subst.compose_ren_right, Subst.cons]; funext; case _ i =>
  cases i <;> simp

@[simp]
theorem Subst.compose_ren_left_cons_lift {σ : Subst S} {r : Ren S} : r.lift ∘ (x :: σ) = x :: r ∘ σ := by
  simp [Subst.compose_ren_left, Subst.cons]; funext; case _ i =>
  cases i <;> simp

theorem Subst.compose_ren_append_id_commute_indirect [RenMap S S] {ℓ : List $ Action S} {r : Ren S} (h : k = ℓ.length)
  : (ℓ ++ Subst.id S) ∘ r = r.lift k ∘ (ℓ⟨r⟩ ++ Subst.id S)
:= by
  induction ℓ generalizing r k; simp [*]
  case _ hd tl ih =>
    simp [-Subst.rewrite_lift_k_ren] at *
    rw [@ih (k - 1) r (by simp [*])]
    cases k; simp at h; case _ k =>
    simp [-Subst.rewrite_lift_k_ren]
    rw [Ren.lift_of_succ, Subst.compose_ren_left_cons_lift]

theorem Subst.compose_ren_append_id_commute_direct [RenMap S S] {ℓ : List $ Action S} {r : Ren S}
  : (ℓ ++ Subst.id S) ∘ r = r.lift ℓ.length ∘ (ℓ⟨r⟩ ++ Subst.id S)
:= by
  rw [compose_ren_append_id_commute_indirect rfl]

theorem PatternBinders.rename_type Δr (r : Ren Ty) (wf : ⊢ G) (h : ∀ i, Δ[i]? = Δr[r.act i]?) :
  PatternBinders G Δ m S p ζ ξ -> PatternBinders G Δr m S⟨r⟩ p⟨r⟩ ζ ξ⟨r.lift ζ.length⟩
| zero => zero
| @succ G Δ nc c na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' e1 j1 e2 e3 e4 j2 =>
  have e1' : lookup_spine_type G c = (some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩)⟨r⟩ := by
    have lem := GlobalWf.closed_lookup_spine_type_ren wf e1 r
    simp; simp at lem; grind
  have j1' := λ i => (j1 i).rename Δr r h
  have j2' := j2.rename_type Δr r wf h
  have e2' : Ts'⟨r.lift (nb + ℓ1.length)⟩ = (Vec.map (fun x => x⟨r.lift (na + nb)⟩) Ts)[(List.map su As⟨r⟩.list.reverse ++ Subst.id Ty).lift nb]⟨Ren.add Ty ℓ1.length⟩ := by
    rw [e2, Vec.rmap_promote]; simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]; congr 1
    rw [Ren.lift_of_add, <-Subst.compose_commute_add_ren_ren]
    rw [<-Subst.rewrite7_ren, <-Subst.lift_compose_ren_right, Subst.compose_ren_append_id_commute_direct]
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    rw [Ren.lift_of_add, <-Subst.rewrite_lift_compose_ren_left]; congr
    have lem : (List.map su As⟨r⟩.list).reverse = (List.map su As.list).reverse⟨r⟩ := by simp
    rw [lem, <-Subst.compose_ren_append_id_commute_indirect]
    all_goals simp
  have e3' : ℓ2'⟨r.lift (nb + ℓ1.length)⟩ = ℓ2⟨r.lift ℓ1.length⟩⟨(Ren.add Ty nb).lift ℓ1.length⟩ := by
    rw [e3]; simp [-Subst.rewrite_lift_k_ren]
    rw [Ren.lift_of_add, <-Ren.lift_compose, <-Subst.compose_commute_add_ren_ren]
    rw [<-Ren.lift_compose]
  have e4' : R'⟨r⟩⟨.add Ty nb⟩ = R⟨r.lift (na + nb)⟩[(List.map su As⟨r⟩.list.reverse ++ Subst.id Ty).lift nb] := by
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]; rw [Subst.compose_commute_add_ren_ren]
    rw [<-Ren.apply_compose, e4]; simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
    congr; rw [<-Subst.lift_compose_ren_right, Subst.compose_ren_append_id_commute_direct]
    rw [Ren.lift_of_add, Subst.rewrite_lift_compose_ren_left]
    simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_k]
  succ (Ts' := Ts'⟨r.lift (nb + ℓ1.length)⟩) (ℓ2' := ℓ2'⟨r.lift (nb + ℓ1.length)⟩)
    e1' (j1' ▸ simp) e2' e3' e4' j2' ▸ congr; simp

theorem Query.Match.rename_type (r : Ren Ty) :
  Query.Match q p -> Query.Match q p⟨r⟩
| .nil => .nil
| .cons ⟨na, As, nb, e⟩ j2 =>
  let j2' := Query.Match.rename_type r j2
  .cons ⟨na, As⟨r⟩, nb, by grind⟩ j2'

@[simp]
theorem Ren.List.length_rmap [RenMap S T] {ℓ : List S} {r : Ren T} : ℓ⟨r⟩.length = ℓ.length := by
  induction ℓ <;> simp [*]

@[simp]
theorem Pattern.bind_zero : {p : Pattern 0} -> p.bind = 0
| .nil => by simp [Pattern.bind]

theorem PatternBinders.length : PatternBinders G Δ m S p ζ ξ -> p.bind = ξ.length
| zero => by simp
| succ j1 j2 e1 e2 e3 j3 => by
  have lem := j3.length
  simp [Pattern.bind, e2]; grind

@[simp]
theorem Pattern.bind_type_zero : {p : Pattern 0} -> p.bind_type = 0
| .nil => by simp [Pattern.bind_type]

theorem PatternBinders.length_type : PatternBinders G Δ m S p ζ ξ -> p.bind_type = ζ.length
| zero => by simp
| succ j1 j2 e1 e2 e3 j3 => by
  have lem := j3.length_type
  simp [Pattern.bind_type]; grind

theorem Typing.rename_type Δr (r : Ren Ty) (wf : ⊢ G) (h : ∀ i, Δ[i]? = Δr[r.act i]?)
  : G&Δ,Γ ⊢ t : A -> G&Δr,Γ⟨r⟩ ⊢ t⟨r⟩ : A⟨r⟩
| var (x := x) j1 j2 =>
  have lem : Γ[x]?⟨r⟩ = (some A)⟨r⟩ := by rw [j1]
  var (by simp at lem; exact lem) (j2.rename _ _ h)
| defn (x := x) (t := t) j1 j2 =>
  have j1' : lookup_defn G x = some (A⟨r⟩, t⟨r⟩) := by
    have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn_ren wf j1
    rw [e1 r, e3 r]; exact j1
  defn j1' (j2.rename _ _ h)
| @spctor G Δ Γ m1 m2 n x v Ks1 Ks2 Ts Ts' R R' As Bs ts j1 e1 e2 j2 j3 j4 j5 j6 =>
  have j1' : lookup_spine_type G x = (some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩)⟨r⟩ := by
    have lem := GlobalWf.closed_lookup_spine_type_ren wf j1 r
    simp; simp at lem; grind
  have e1' : Ts'⟨r⟩ = Ts⟨r.lift (m1 + m2)⟩[List.map su (As⟨r⟩.list ++ Bs⟨r⟩.list).reverse ++ Subst.id Ty] := by
    rw [e1]; simp [-Subst.rewrite_lift_k_ren];
    generalize ℓdef : (List.map su Bs.list).reverse ++ (List.map su As.list).reverse = ℓ
    have lem : (List.map su Bs⟨r⟩.list).reverse ++ (List.map su As⟨r⟩.list).reverse = ℓ⟨r⟩ := by
      rw [<-ℓdef]; simp
    rw [lem]
    generalize kdef : m1 + m2 = k
    have lem2 := Subst.List.rmap_map_su (ℓ := Bs.list) (r := r)
    rw [<-Subst.compose_ren_append_id_commute_indirect]; simp
    rw [<-ℓdef]; simp; rw [<-kdef]; omega
  have e2' : R'⟨r⟩ = R⟨r.lift (m1 + m2)⟩[List.map su (As⟨r⟩.list ++ Bs⟨r⟩.list).reverse ++ Subst.id Ty] := by
    rw [e2]; simp [-Subst.rewrite_lift_k_ren]
    generalize ℓdef : (List.map su Bs.list).reverse ++ (List.map su As.list).reverse = ℓ
    have lem : (List.map su Bs⟨r⟩.list).reverse ++ (List.map su As⟨r⟩.list).reverse = ℓ⟨r⟩ := by
      rw [<-ℓdef]; simp
    rw [lem]
    rw [<-Subst.compose_ren_append_id_commute_indirect]; simp
    rw [<-ℓdef]; simp; omega
  have j2' : ∀ (i : Fin m1), G&Δr ⊢ As⟨r⟩[i] : Ks1[i] := λ i =>
    let lem := (j2 i).rename Δr r h
    by simp at lem; exact lem
  have j3' : ∀ (i : Fin m2), G&Δr ⊢ Bs⟨r⟩[i] : Ks2[i] := λ i =>
    let lem := (j3 i).rename Δr r h
    by simp at lem; exact lem
  have j4' : ∀ (i : Fin n), G&Δr,Γ⟨r⟩ ⊢ (ts i)⟨r⟩ : Ts'[i]⟨r⟩ := λ i =>
    let lem := (j4 i).rename_type Δr r wf h
    by simp at lem; simp; exact lem
  have j5' : ∀ c, v = .data c → lookup_ctor? G c x R⟨r.lift (m1 + m2)⟩ = true :=
    have lem := GlobalWf.closed_lookup_spine_type_ren wf j1 r
    by simp at lem; simp; rw [lem.2]; exact j5
  have j6' : v = .openm → ∀ (i : Fin n), Ty.data? DataConst.opn G Ts⟨r.lift (m1 + m2)⟩[i] := λ e i =>
    Ty.data?_closed_ren (r.lift (m1 + m2)) (j6 e i) ▸ simp
  spctor (Ts := Ts⟨r.lift (m1 + m2)⟩) (R := R⟨r.lift (m1 + m2)⟩)
    (j1' ▸ simp) e1' e2' j2' j3' (λ i => j4' i ▸ simp [Term.Ty.rmap_promote]) j5' j6'
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ζ := ζ) (ξ := ξ) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).rename_type Δr r wf h
  have j2' := λ i => Ty.data?_closed_ren r (j2 i)
  let ξ' := λ (i : Fin n) => (ξ i)⟨r.lift (ζ i).length⟩
  have j3' : ∀ (i : Fin n), PatternBinders G Δr m S.to⟨r⟩ (ps i)⟨r⟩ (ζ i) (ξ' i) :=
    λ i => (j3 i).rename_type Δr r wf h
  have j4' : ∀ (i : Fin n), G&(ζ i ++ Δr),((ξ' i) ++ Γ⟨r⟩⟨.add Ty (ζ i).length⟩) ⊢ (ts i)⟨r.lift (ps i).bind_type⟩ : A⟨r⟩⟨.add Ty (ζ i).length⟩ := λ i => by
    have lem1 := rename_type_lift_k (ζ i) h
    have lem2 : (ζ i).length = (ps i).bind_type := Eq.symm (j3 i).length_type
    rw [lem2] at lem1
    have lem3 := (j4 i).rename_type (ζ i ++ Δr) (r.lift (ps i).bind_type) wf lem1
    rw [lem2] at lem3; simp [-Subst.rewrite_lift_k_ren] at lem3
    rw [<-Subst.compose_commute_add_ren_ren] at lem3
    simp [-Subst.rewrite_lift_k_ren, lem2, ξ']; exact lem3
  have j5' : ∀ {q}, (Query G .cls q S⟨r⟩) → ∃ i, Query.Match q (ps i)⟨r⟩ :=
    λ q => match j5 (Query.closed_ren wf rfl q) with
          | ⟨i, m⟩ => ⟨i, Query.Match.rename_type r m⟩
  mtch (ζ := ζ) (ξ := ξ') j1' j2'
    (λ i => j3' i ▸ congr 1; grind)
    (λ i => (j4' i) ▸ congr 1)
    (λ {q} => @j5' q ▸ grind)
| lam j1 j2 => lam (j1.rename Δr r h) (j2.rename_type _ _ wf h)
| app j1 j2 => app (j1.rename_type _ _ wf h) (j2.rename_type _ _ wf h)
| lamt (K := K) (P := P) (t := t) j1 j2 =>
  let j2' : G&(K :: Δr),Γ⟨r⟩⟨.succ Ty⟩ ⊢ t⟨r.lift⟩ : P⟨r.lift⟩ := by
    have lem := j2.rename_type (K::Δr) r.lift wf (Typing.rename_type_lift K h)
    grind
  lamt (j1.rename Δr r h) j2'
| appt (P := P) j1 j2 e =>
  appt (P := P⟨r.lift⟩) (j1.rename_type Δr r wf h) (j2.rename Δr r h) (by simp [e])
| refl j1 => refl (j1.rename Δr r h)
| cast (K := K) (A := A) (R := R) (R' := R') (c := c) (t := t) j1 j2 j3 e =>
  let j1' := j1.rename _ _ (Kinding.rename_lift _ _ h)
  let j2' := j2.rename_type Δr r wf h
  let j3' : G&Δr,Γ⟨r⟩ ⊢ t⟨r⟩ : R⟨r.lift⟩[su A⟨r⟩ :: +0σ] :=
    have lem := j3.rename_type Δr r wf h
    by simp; simp at lem; exact lem
  let lem : G&Δr,Γ⟨r⟩ ⊢ .cast R⟨r.lift⟩ c⟨r⟩ t⟨r⟩ : R'⟨r⟩ :=
    cast j1' j2' j3' (by simp [e]; congr)
  by simp; simp at lem; exact lem
| prj j1 j2 => prj (j1.rename_type _ _ wf h) (j2.rename_type _ _ h)
| allc (K := K) (A := A) (B := B) (t := t) j1 =>
  have j1' : G&(K::Δr),Γ⟨r⟩⟨.succ Ty⟩ ⊢ t⟨r.lift⟩ : (A⟨r.lift⟩ ~[★]~ B⟨r.lift⟩) := by
    have lem := j1.rename_type (K::Δr) r.lift wf (Typing.rename_type_lift K h)
    simp; simp at lem; exact lem
  allc j1'
| apptc j1 j2 e1 e2 =>
  let j1' := j1.rename_type _ _ wf h
  let j2' := j2.rename_type _ _ wf h
  apptc j1' j2' (by simp [Ty.rmap_promote, e1]) (by simp [Ty.rmap_promote, e2])

theorem Typing.rename Γr (r : Ren Term) (wf : ⊢ G)
  (h : ∀ {i}, Γ[i]? = Γr[r.act i]?)
  : G&Δ,Γ ⊢ t : A ->
  G&Δ,Γr ⊢ t⟨r⟩ : A
| var (x := x) j1 j2 => var (j1 ▸ by rw [<-h]) j2
| defn (x := x) (t := t) j1 j2 =>
  have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn_ren wf j1
  have j1' : lookup_defn G x = some (A, t⟨r⟩) := by
    rw [e2 r]; exact j1
  defn j1' j2
| spctor j1 e1 e2 j2 j3 j4 j5 j6 => spctor j1 e1 e2 j2 j3 (λ i => (j4 i).rename _ _ wf h) j5 j6
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ζ := ζ) (ξ := ξ) j1 j2 j3 j4 j5 =>
  have j4' : ∀ (i : Fin n), G&(ζ i ++ Δ),(ξ i ++ Γr⟨Ren.add Ty (ζ i).length⟩) ⊢ (ts i)⟨r.lift (ps i).bind⟩ : A⟨Ren.add Ty (ζ i).length⟩ := λ i =>
    have lem1 : (ps i).bind = (ξ i).length := (j3 i).length
    have lem {k} : (ξ i ++ Γ⟨Ren.add Ty (ζ i).length⟩)[k]? = (ξ i ++ Γr⟨Ren.add Ty (ζ i).length⟩)[(r.lift (ps i).bind).act k]? := by
      rw [lem1]
      have h2 {j} := Typing.rename_rename r (Ren.add Ty (ζ i).length) h (i := j)
      simp at h2
      have h3 {j} := Typing.rename_lift_k r (ξ i) h2 (i := j)
      exact h3
    (j4 i).rename (ξ i ++ Γr⟨Ren.add Ty (ζ i).length⟩) (r.lift (ps i).bind) wf lem
  mtch (λ i => (j1 i).rename _ _ wf h) j2 j3 j4' j5
| lam (A := A) j1 j2 =>
  let j2' := (j2.rename (A::Γr) r.lift wf (Typing.rename_lift _ A h) ▸ simp [Term.rmap_promote])
  lam j1 j2'
| app j1 j2 => app (j1.rename _ _ wf h) (j2.rename _ _ wf h)
| lamt j1 j2 =>
  have lem {i} : Γ[i]?⟨.succ Ty⟩ = Γr[r.act i]?⟨.succ Ty⟩ := by rw [@h i]
  lamt j1 (j2.rename _ _ wf (by simp at lem; exact lem))
| appt (P := P) j1 j2 e => appt (j1.rename _ _ wf h) j2 (by simp [*])
| refl j1 => refl j1
| cast j1 j2 j3 e => cast j1 (j2.rename _ _ wf h) (j3.rename _ _ wf h) e
| prj j1 j2 => prj (j1.rename _ _ wf h) j2
| allc j1 =>
  have lem {i} : Γ[i]?⟨.succ Ty⟩ = Γr[r.act i]?⟨.succ Ty⟩ := by rw [@h i]
  allc (j1.rename _ _ wf (by simp at lem; exact lem))
| apptc j1 j2 e1 e2 => apptc (j1.rename _ _ wf h) (j2.rename _ _ wf h) e1 e2

theorem Typing.weaken T : ⊢ G -> G&Δ,Γ ⊢ t : A -> G&Δ,(T::Γ) ⊢ t⟨.succ Term⟩ : A := by
  intro wf j; apply rename (T::Γ) (.succ Term) wf _ j; simp

theorem Typing.weaken_list Γ' :
  ⊢ G ->
  G&Δ,Γ ⊢ t : A ->
  G&Δ,(Γ'++Γ) ⊢ t⟨.add Term Γ'.length⟩ : A
:= by
  intro wf j; apply rename (Γ'++Γ) (.add Term Γ'.length) wf _ j
  intro i; simp
  rw [List.getElem?_append_right]; simp; omega

theorem Typing.weaken_type_list Δ' :
  ⊢ G ->
  G&Δ,Γ ⊢ t : A ->
  G&(Δ'++Δ),Γ⟨.add Ty Δ'.length⟩ ⊢ t⟨.add Ty Δ'.length⟩ : A⟨.add Ty Δ'.length⟩
:= by
  intro wf j; apply rename_type (Δ'++Δ) (.add Ty Δ'.length) wf _ j
  intro i; simp
  rw [List.getElem?_append_right]; simp; simp

theorem Kinding.strengthening :
  G&(K' :: Δ) ⊢ T⟨.succ Ty⟩ : K ->
  G&Δ ⊢ T : K := by
intro j
have lem := Kinding.strong_rename (Δ := K' :: Δ) (Δr := Δ) (r := .pred Ty) (T := T⟨.succ Ty⟩) j
  (by intro x h; simp at *
      induction x <;> simp at *
      case zero => exfalso; apply FV.zero_not_in_succ h)
simp at lem; apply lem

end Core
