
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

theorem CoercionProject.rename_type Δr (r : Ren Ty) (h : ∀ i, Δ[i]? = Δr[r.act i]?)
  : CoercionProject G Δ n T A -> CoercionProject G Δr n T⟨r⟩ A⟨r⟩
| fst_app j => fst_app (j.rename _ _ h)
| snd_app j => snd_app (j.rename _ _ h)
| fst_arrow j => fst_arrow (j.rename _ _ h)
| snd_arrow j => snd_arrow (j.rename _ _ h)

theorem test {r1 r2 : Ren Ty} {Δ Δ1 Δ2 : List Kind}
  (h1 : ∀ i, Δ[i]? = Δ1[r1.act i]?)
  (h2 : ∀ i, Δ[i]? = Δ2[r2.act i]?)
  : r1 ∘ r2 = r2 ∘ r1
:= by
  simp [Ren.compose]; funext; case _ i =>

  induction i
  case zero => sorry
  case succ i ih =>

    sorry

theorem PatternBinders.rename_type Δr (r : Ren Ty) (wf : ⊢ G) (h : ∀ i, Δ[i]? = Δr[r.act i]?) :
  PatternBinders G Δ m S p ζ ξ -> PatternBinders G Δr m S⟨r⟩ p⟨r⟩ ζ ξ⟨.add Ty ζ.length ∘ r⟩
| zero => zero
| @succ G Δ nc c na Ks1 nb Ks2 Ts R As ℓ2' ℓ2 R' n S p ℓ1 Ts' e1 j1 e2 e3 e4 j2 =>
  have e1' : lookup_spine_type G c = (some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩)⟨r⟩ := by
    have lem := GlobalWf.closed_lookup_spine_type_ren wf e1 r
    simp; simp at lem; grind
  have j1' := λ i => (j1 i).rename Δr r h
  have j2' := j2.rename_type Δr r wf h
  have e2' : Ts'⟨Ren.add Ty (nb + ℓ1.length) ∘ r⟩ = (Vec.map (fun x => x⟨r.lift (na + nb)⟩) Ts)[(List.map su As⟨r⟩.list.reverse ++ Subst.id Ty).lift nb]⟨Ren.add Ty ℓ1.length⟩ := by
    sorry
  have e3' : ℓ2'⟨Ren.add Ty (nb + ℓ1.length) ∘ r⟩ = ℓ2⟨Ren.add Ty ℓ1.length ∘ r⟩⟨Ren.add Ty ℓ1.length⟩ := by
    rw [e3];
    sorry
  have e4' : R'⟨r⟩ = R⟨r.lift (na + nb)⟩[(List.map su As⟨r⟩.list.reverse ++ Subst.id Ty).lift nb]⟨Ren.sub Ty nb⟩ := by
    rw [e4]
    sorry
  succ (Ts' := Ts'⟨Ren.add Ty (nb + ℓ1.length) ∘ r⟩) (ℓ2' := ℓ2'⟨Ren.add Ty (nb + ℓ1.length) ∘ r⟩)
    e1' (j1' ▸ simp) e2' e3' e4' j2' ▸ congr; simp

theorem Query.Match.rename_type (r : Ren Ty) :
  Query.Match q p -> Query.Match q p⟨r⟩
| .nil => .nil
| .cons ⟨na, As, nb, e⟩ j2 =>
  let j2' := Query.Match.rename_type r j2
  .cons ⟨na, As⟨r⟩, nb, by grind⟩ j2'

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
  sorry

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
  sorry

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
    have lem : (List.map su Bs⟨r⟩.list).reverse ++ (List.map su As⟨r⟩.list).reverse = ℓ⟨r⟩ := sorry
    rw [lem]
    generalize kdef : m1 + m2 = k
    have lem2 := Subst.List.rmap_map_su (ℓ := Bs.list) (r := r)
    rw [Subst.List.rmap_map_su (ℓ := As.list) (r := r)]
    rw [Subst.compose_ren_left_cons_lift_indirect (k := k) (ℓ := ℓ⟨r⟩)]

    sorry
  have e2' : R'⟨r⟩ = R⟨r.lift (m1 + m2)⟩[List.map su (As⟨r⟩.list ++ Bs⟨r⟩.list).reverse ++ Subst.id Ty] := by
    rw [e2]; simp; sorry
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
  have j3' : ∀ (i : Fin n), PatternBinders G Δr m S.to⟨r⟩ (ps i)⟨r⟩ (ζ i) (ξ i)⟨r⟩ :=
    λ i => (j3 i).rename_type Δr r wf h
  have j4' : ∀ (i : Fin n), G&(ζ i ++ Δr),((ξ i)⟨r⟩ ++ Γ⟨r⟩)⟨Ren.add Ty (ζ i).length⟩ ⊢ (ts i)⟨r.lift (ps i).bind_type⟩ : A⟨r⟩⟨Ren.add Ty (ζ i).length⟩ := λ i => by
    have lem1 := rename_type_lift_k (ζ i) h
    have lem2 : (ζ i).length = (ps i).bind_type := sorry
    rw [lem2] at lem1
    have lem3 := (j4 i).rename_type (ζ i ++ Δr) (r.lift (ps i).bind_type) wf lem1
    rw [lem2] at lem3; simp [-Subst.rewrite_lift_k_ren] at lem3
    rw [<-Subst.compose_commute_add_ren_ren] at lem3
    simp [-Subst.rewrite_lift_k_ren, lem2]; exact lem3
  have j5' : ∀ {q}, (Query G .cls q S⟨r⟩) → ∃ i, Query.Match q (ps i)⟨r⟩ :=
    λ q => match j5 (Query.closed_ren wf rfl q) with
          | ⟨i, m⟩ => ⟨i, Query.Match.rename_type r m⟩
  let ξ' := λ (i : Fin n) => (ξ i)⟨r⟩
  mtch (ζ := ζ) (ξ := ξ') j1' j2' (λ i => j3' i ▸ congr; grind) (j4' ▸ simp [ξ', Term.Ty.rmap_promote]) (λ {q} => @j5' q ▸ grind)
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

@[simp]
theorem Pattern.bind_zero : {p : Pattern 0} -> p.bind = 0
| .nil => by simp [Pattern.bind]

theorem PatternBinders.length : PatternBinders G Δ m S p ζ ξ -> p.bind = ξ.length
| zero => by simp
| succ j1 j2 e1 e2 e3 j3 => by
  have lem := j3.length
  simp [Pattern.bind, e2]; grind

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
| spctor j1 e1 e2 j2 j3 j4 j5 j6 => sorry --spctor j1 e1 e2 j2 (λ i => (j3 i).rename _ _ wf h) j4 j5
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ξ := ξ) j1 j2 j3 j4 j5 =>
  sorry
  -- let j4' : ∀ (i : Fin n), G&Δ,(ξ i ++ Γr) ⊢ (ts i)[r.to.lift (ps i).bind] : A := λ i =>
  --   have lem1 : (ps i).bind = (ξ i).length := (j3 i).length
  --   have lem {k} : (ξ i ++ Γ)[k]? = (ξ i ++ Γr)[(r.lift (ps i).bind).act k]? := by
  --     rw [lem1]; exact Typing.rename_lift_k r (ξ i) h
  --   (j4 i).rename (ξ i ++ Γr) (r.lift (ps i).bind) wf lem ▸ sorry --rw [Ren.to_lift]
  -- mtch (λ i => (j1 i).rename _ _ wf h) j2 j3 sorry j5
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
