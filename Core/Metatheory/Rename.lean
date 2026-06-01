
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

theorem Kinding.strong_rename_lift {T : Ty} {Δr Δ : List Kind} {r : Ren} K :
  (∀ x, x + 1 ∈ T -> Δr[r x]? = Δ[x]?) ->
  ∀ x, x ∈ T -> (K::Δr)[r.lift 1 x]? = (K ::Δ)[x]? := by
intro h1 x h2
induction x
case _ => simp [Ren.lift] at *
case succ n ih =>
  replace h1 := h1 n h2
  simp [Ren.lift]; assumption

theorem Kinding.strong_rename {Δ Δr : List Kind} {T : Ty} (r : Ren)  :
  G&Δ ⊢ T : K ->
  (∀ x : Nat,  x ∈ T -> Δr[r x]? = Δ[x]?) ->
  G&Δr ⊢ T[r] : K := by
intro j h
induction j generalizing Δr r <;> simp [-rewrite_lift_n] at *
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
  have lem : ∀ (x : Nat), x + 1 ∈ P → (Δr)[r x]? = Δ[x]? := by
    intro i x
    replace x := Ty.FV.all (K := K) x
    replace h := @h i x; simp at h; assumption
  replace lem := Kinding.strong_rename_lift K lem
  apply Kinding.all
  replace ih := @ih (K :: Δr) r.lift
  simp [-rewrite_lift_n] at ih; grind

theorem Kinding.rename_lift {Δ Δr : List Kind} K (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  ∀ i, (K::Δ)[i]? = (K::Δr)[r.lift 1 i]?
:= by
  intro h i
  cases i <;> simp [Ren.lift] at *
  case _ i => exact h i

theorem Kinding.rename Δr (r : Ren) :
  (∀ i, Δ[i]? = Δr[r i]?) ->
  G&Δ ⊢ A : K ->
  G&Δr ⊢ A[r] : K
:= by
  intro h j
  apply Kinding.strong_rename _ j
  intro x _ ; replace h := @h x; symm at h; assumption

theorem Kinding.weaken T : G&Δ ⊢ A : K -> G&(T::Δ) ⊢ A[+1] : K := by
  intro j; apply rename (T::Δ) (· + 1) _ j
  intro i; cases i <;> simp

theorem CoercionProject.rename_type Δr (r : Ren) (h : ∀ i, Δ[i]? = Δr[r i]?)
  : CoercionProject G Δ n T A -> CoercionProject G Δr n T[r.to:Ty] A[r.to:Ty]
| fst_app j => fst_app (j.rename _ _ h)
| snd_app j => snd_app (j.rename _ _ h)
| fst_arrow j => fst_arrow (j.rename _ _ h)
| snd_arrow j => snd_arrow (j.rename _ _ h)

theorem PatternBinders.rename_type Δr (r : Ren) (wf : ⊢ G) (h : ∀ i, Δ[i]? = Δr[r i]?) :
  PatternBinders G Δ m S p ξ -> PatternBinders G Δr m S[r.to:Ty] p[r.to:Ty] ξ[r.to:Ty]
| zero => zero
| @succ G Δ nb c na Ks Ts R As R' n S p ℓ Ts' e1 j1 e2 e3 j2 =>
  have e1' : lookup_spine_type G c = (some ⟨na, (Ks, ⟨nb, (Ts, R)⟩)⟩)[r.to:Ty] := by
    have lem := GlobalWf.closed_lookup_spine_type wf e1 r.to
    simp; simp at lem; grind
  have e2' : Ts'[r.to:Ty] = (Vec.map (·[r.to.lift na:Ty]) Ts)[Sequ.append_vec (Vec.map su As[r.to:Ty]) +0:_] := by
    rw [e2]; simp
  have e3' : R'[r.to:Ty] = R[r.to.lift na][Sequ.append_vec (Vec.map su As[r.to:Ty]) +0:_] := by
    rw [e3]; simp
  have j1' := λ i => (j1 i).rename Δr r h
  have j2' := j2.rename_type Δr r wf h
  succ e1' (j1' ▸ simp) e2' e3' j2' ▸ congr; simp

theorem Query.Match.rename_type (r : Ren) :
  Query.Match q p -> Query.Match q p[r:Ty]
| .nil => .nil
| .cons ⟨na, As, nb, e⟩ j2 =>
  let j2' := Query.Match.rename_type r j2
  .cons ⟨na, As[r.to:Ty], nb, by grind⟩ j2'

theorem Typing.rename_lift {Γ Γr : List Ty} (r : Ren) T :
  (∀ {i}, Γ[i]? = Γr[r i]?) ->
  ∀ {i}, (T::Γ)[i]? = (T::Γr)[r.lift 1 i]?
:= by
  intro h1 i
  cases i <;> simp [Ren.lift] at *
  case _ => exact h1

theorem Typing.rename_lift_k {Γ Γr : List Ty} (r : Ren) T :
  (∀ {i}, Γ[i]? = Γr[r i]?) ->
  ∀ {i}, (T ++ Γ)[i]? = (T ++ Γr)[r.lift T.length i]?
:= by
  sorry

theorem Typing.rename_type_lift {Δ Δr : List Kind} {r : Ren} K :
  (∀ (i : Nat), Δ[i]? = Δr[r i]?) ->
  ∀ (i : Nat), (K :: Δ)[i]? = (K :: Δr)[r.lift 1 i]?
:= by
  intro h i
  cases i <;> simp [Ren.lift]
  apply h _

theorem Typing.rename_type Δr (r : Ren) (wf : ⊢ G) (h : ∀ i, Δ[i]? = Δr[r i]?)
  : G&Δ,Γ ⊢ t : A -> G&Δr,Γ[r:Ty] ⊢ t[r:Ty] : A[r]
| var (x := x) j1 j2 =>
  have lem : Γ[x]?[r.to:Ty] = (some A)[r.to:Ty] := by rw [j1]
  var (by simp at lem; exact lem) (j2.rename _ _ h)
| defn (x := x) (t := t) j1 j2 =>
  have j1' : lookup_defn G x = some (A[r:Ty], t[r:Ty]) := by
    have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn wf j1
    rw [e1 r.to, e3 r.to]; exact j1
  defn j1' (j2.rename _ _ h)
| @spctor G Δ Γ m n x v Ks Ts Ts' R R' As ts j1 e1 e2 j2 j3 j4 j5 =>
  have j1' : lookup_spine_type G x = (some ⟨m, (Ks, ⟨n, (Ts, R)⟩)⟩)[r.to:Ty] := by
    have lem := GlobalWf.closed_lookup_spine_type wf j1 r.to
    simp; simp at lem; grind
  have e1' : Ts'[r.to:Ty] = (Vec.map (·[r.to.lift m:Ty]) Ts)[Sequ.append_vec (Vec.map su As[r.to:Ty]) +0:_] := by
    rw [e1]; simp
  have e2' : R'[r.to:Ty] = R[r.to.lift m][Sequ.append_vec (Vec.map su As[r.to:Ty]) +0:_] := by
    rw [e2]; simp
  have j2' : ∀ (i : Fin m), G&Δr ⊢ As[r.to:_][i] : Ks[i] := λ i =>
    let lem := (j2 i).rename Δr r h
    by simp at lem; exact lem
  have j3' : ∀ (i : Fin n), G&Δr,Γ[r.to:Ty] ⊢ (ts i)[r.to:Ty] : Ts'[i][r.to] := λ i =>
    let lem := (j3 i).rename_type Δr r wf h
    by simp at lem; simp; exact lem
  have j4' : ∀ c, v = .data c → lookup_ctor? G c x R[r.to.lift m] = true :=
    have lem := GlobalWf.closed_lookup_spine_type wf j1 r.to
    by simp at lem; simp; rw [lem.2]; exact j4
  have j5' : v = .openm → ∀ (i : Fin n), Ty.data? DataConst.opn G Ts'[r.to:Ty][i] := λ e i =>
    Ty.data?_closed r.to (j5 e i) ▸ simp
  spctor j1' e1' e2' j2' (λ i => j3' i ▸ congr; simp) j4' j5'
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ξ := ξ) j1 j2 j3 j4 j5 =>
  have j1' := λ i => (j1 i).rename_type Δr r wf h
  have j2' := λ i => Ty.data?_closed r.to (j2 i)
  have j3' : ∀ (i : Fin n), PatternBinders G Δr m S.to[r.to:Ty] (ps i)[r.to:Ty] (ξ i)[r.to:Ty] :=
    λ i => (j3 i).rename_type Δr r wf h
  have j4' : ∀ (i : Fin n), G&Δr,((ξ i)[r.to:Ty] ++ Γ[r.to:Ty]) ⊢ (ts i)[r.to:Ty] : A[r.to] :=
    λ i => (j4 i).rename_type Δr r wf h ▸ simp
  have j5' : ∀ {q}, (Query G .cls q S[r.to:Ty]) → ∃ i, Query.Match q (ps i)[r.to:Ty] :=
    λ q => match j5 (Query.closed wf rfl q) with
          | ⟨i, m⟩ => ⟨i, Query.Match.rename_type r m⟩
  let ξ' := λ (i : Fin n) => (ξ i)[r.to:Ty]
  mtch (ξ := ξ') j1' j2' (λ i => j3' i ▸ subst ξ'; congr; grind) j4' (λ {q} => @j5' q ▸ grind)
| lam j1 j2 => lam (j1.rename Δr r h) (j2.rename_type _ _ wf h)
| app j1 j2 => app (j1.rename_type _ _ wf h) (j2.rename_type _ _ wf h)
| lamt (K := K) (P := P) (t := t) j1 j2 =>
  let j2' : G&(K :: Δr),Γ[r.to:Ty][+1:Ty] ⊢ t[r.to.lift:Ty] : P[r.to.lift] := by
    have lem := j2.rename_type (K::Δr) r.lift wf (Typing.rename_type_lift K h)
    rw [Ren.to_lift] at lem
    simp; simp at lem; exact lem
  lamt (j1.rename Δr r h) j2'
| appt (P := P) j1 j2 e =>
  appt (P := P[r.to.lift]) (j1.rename_type Δr r wf h) (j2.rename Δr r h) (by simp [*])
| refl j1 => refl (j1.rename Δr r h)
| cast (K := K) (A := A) (R := R) (R' := R') (c := c) (t := t) j1 j2 j3 e =>
  let j1' : G&(K::Δr) ⊢ R[r.to.lift] : ★ :=
    have lem := j1.rename _ _ (Kinding.rename_lift _ _ h)
    by rw [Ren.to_lift] at lem; exact lem
  let j2' := j2.rename_type Δr r wf h
  let j3' : G&Δr,Γ[r:Ty] ⊢ t[r.to:Ty] : R[r.to.lift:Ty][su A[r:Ty] :: +0] :=
    have lem := j3.rename_type Δr r wf h
    by simp_all
  let lem : G&Δr,Γ[r:Ty] ⊢ .cast R[r.to.lift:Ty] c[r:Ty] t[r:Ty] : R'[r:Ty] :=
    cast j1' j2' j3' (by rw [e]; simp; congr)
  by simp; simp at lem; exact lem
| prj j1 j2 => prj (j1.rename_type _ _ wf h) (j2.rename_type _ _ h)
| allc (K := K) (A := A) (B := B) (t := t) j1 =>
  have j1' : G&(K::Δr),Γ[r.to:Ty][+1:Ty] ⊢ t[r.to.lift:Ty] : (A[r.to.lift] ~[★]~ B[r.to.lift]) := by
    have lem := j1.rename_type (K::Δr) r.lift wf (Typing.rename_type_lift K h)
    rw [Ren.to_lift] at lem
    simp; simp at lem; exact lem
  allc j1'
| apptc j1 j2 e1 e2 =>
  let j1' := j1.rename_type _ _ wf h
  let j2' := j2.rename_type _ _ wf h
  apptc j1' j2' (by simp [Ty.smap_promote, e1]) (by simp [Ty.smap_promote, e2])

@[simp]
theorem Pattern.bind_zero : {p : Pattern 0} -> p.bind = 0
| .nil => by simp [Pattern.bind]

theorem PatternBinders.length : PatternBinders G Δ m S p ξ -> p.bind = ξ.length
| zero => by simp
| succ j1 j2 e1 e2 j3 => by simp [Pattern.bind]; exact j3.length

theorem Typing.rename Γr (r : Ren) (wf : ⊢ G)
  (h : ∀ {i}, Γ[i]? = Γr[r i]?)
  : G&Δ,Γ ⊢ t : A ->
  G&Δ,Γr ⊢ t[r] : A
| var (x := x) j1 j2 => var (j1 ▸ by rw [<-h]) j2
| defn (x := x) (t := t) j1 j2 =>
  have j1' : lookup_defn G x = some (A, t[r:Term]) := by
    have ⟨e1, e2, e3⟩ := GlobalWf.closed_lookup_defn wf j1
    rw [e2 r.to]; exact j1
  defn j1' j2
| spctor j1 e1 e2 j2 j3 j4 j5 => spctor j1 e1 e2 j2 (λ i => (j3 i).rename _ _ wf h) j4 j5
| mtch (n := n) (m := m) (ts := ts) (ps := ps) (S := S) (ξ := ξ) j1 j2 j3 j4 j5 =>
  let j4' : ∀ (i : Fin n), G&Δ,(ξ i ++ Γr) ⊢ (ts i)[r.to.lift (ps i).bind] : A := λ i =>
    have lem1 : (ps i).bind = (ξ i).length := (j3 i).length
    have lem {k} : (ξ i ++ Γ)[k]? = (ξ i ++ Γr)[r.lift (ps i).bind k]? := by
      rw [lem1]; exact Typing.rename_lift_k r (ξ i) h
    (j4 i).rename (ξ i ++ Γr) (r.lift (ps i).bind) wf lem ▸ rw [Ren.to_lift]
  mtch (λ i => (j1 i).rename _ _ wf h) j2 j3 j4' j5
| lam (A := A) j1 j2 =>
  let j2' := (j2.rename (A::Γr) r.lift wf (Typing.rename_lift _ A h)
    ▸ rw [Ren.to_lift]; simp [Term.smap_promote])
  lam j1 j2'
| app j1 j2 => app (j1.rename _ _ wf h) (j2.rename _ _ wf h)
| lamt j1 j2 =>
  have lem {i} : Γ[i]?[+1:Ty] = Γr[r i]?[+1:Ty] := by rw [@h i]
  lamt j1 (j2.rename _ _ wf (by simp at lem; exact lem))
| appt (P := P) j1 j2 e => appt (j1.rename _ _ wf h) j2 (by simp [*])
| refl j1 => refl j1
| cast j1 j2 j3 e => cast j1 (j2.rename _ _ wf h) (j3.rename _ _ wf h) e
| prj j1 j2 => prj (j1.rename _ _ wf h) j2
| allc j1 =>
  have lem {i} : Γ[i]?[+1:Ty] = Γr[r i]?[+1:Ty] := by rw [@h i]
  allc (j1.rename _ _ wf (by simp at lem; exact lem))
| apptc j1 j2 e1 e2 => apptc (j1.rename _ _ wf h) (j2.rename _ _ wf h) e1 e2

theorem Typing.weaken T : ⊢ G -> G&Δ,Γ ⊢ t : A -> G&Δ,(T::Γ) ⊢ t[+1] : A := by
  intro wf j; apply rename (T::Γ) (· + 1) wf _ j; simp

theorem Typing.weaken_list Γ' :
  ⊢ G ->
  G&Δ,Γ ⊢ t : A ->
  G&Δ,(Γ'++Γ) ⊢ t[Ren.to (· + Γ'.length)] : A
:= by
  intro wf j; apply rename (Γ'++Γ) (· + Γ'.length) wf _ j
  intro i; simp
  rw [List.getElem?_append_right]; simp; omega

theorem Typing.weaken_type_list Δ' :
  ⊢ G ->
  G&Δ,Γ ⊢ t : A ->
  G&(Δ'++Δ),Γ[Ren.to (· + Δ'.length):Ty] ⊢ t[Ren.to (· + Δ'.length):Ty] : A[Ren.to (· + Δ'.length)]
:= by
  intro wf j; apply rename_type (Δ'++Δ) (· + Δ'.length) wf _ j
  intro i; simp
  rw [List.getElem?_append_right]; simp; simp

theorem Kinding.strengthening :
  G&(K' :: Δ) ⊢ T[+1] : K ->
  G&Δ ⊢ T : K := by
intro j
have lem := Kinding.strong_rename (Δ := K' :: Δ) (Δr := Δ) (r := (· - 1)) (T := T[+1]) j
  (by intro x h; simp at *
      induction x <;> simp at *
      case zero => exfalso; apply FV.zero_not_in_succ h)
simp at lem; apply lem

end Core
