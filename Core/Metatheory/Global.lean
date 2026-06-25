
import Core.Vec
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Global

open Lilac

namespace Core

theorem lookup_name_agrees : lookup x G = some e -> e.name = x := by
  intro h; fun_induction lookup <;> simp_all
  all_goals try solve | subst h; simp [Entry.name]
  case _ n y K ctors tl ctors' h2 ih =>
  generalize zdef : lookup x tl = z at *
  replace h := Vec.fold_or h
  cases h
  case _ h => apply ih h
  case _ h => sorry


theorem GlobalWf.drop_wf : ∀ n, ⊢ G -> ⊢ G.drop n := by
  intro n wf
  induction wf generalizing n
  case _ => simp; constructor
  case _ g gwf wf ih =>
  induction n
  case _ => simp; constructor; assumption; assumption
  case _ => simp; apply ih

theorem GlobalWf.drop_lookup_unique_vec :
  {v : Vec (Option Entry) n} ->
  (∀ (i : Fin n), v[i] = none) ->
  v.foldl Option.or (lookup x G) = lookup x G
| .nil, h => by simp
| .cons e tl, h =>
  have lem := h 0
  by
    simp at lem; simp_all
    apply drop_lookup_unique_vec (v := tl)
    intro i; apply h (Fin.succ i)

theorem GlobalWf.drop_lookup_unique {G : List Global} n :
  ⊢ G ->
  lookup x (G.drop n) = some t ->
  lookup x G = some t
:= by
  intro wf j
  induction wf generalizing n <;> simp at *
  case nil => exact j
  case cons G j1 j2 wf ih =>
    cases n <;> simp at *
    case zero => exact j
    case succ n =>
      replace ih := ih n j
      cases j2
      case data n y K ctors j1 j2 j3 =>
        sorry
        -- simp [lookup]; split
        -- case _ e => subst e; rw [ih] at j3; injection j3
        -- case _ e =>
        --   rw [drop_lookup_unique_vec]; exact ih
        --   intro i
        --   generalize endef : ctors i = en at *
        --   rcases en with ⟨z, A⟩; simp; intro e2
        --   replace j2 := j2 i z A endef
        --   rcases j2 with ⟨q1, q2, q3⟩
        --   cases q1; case _ w1 w2 w3 w4 w5 =>
        --   clear w5; replace w4 := w4 _ rfl
        --   simp [lookup_ctor?] at w4; split at w4
        --   case _ =>
        --     have lem : lookup z (Global.data 0 y K #() :: G) = none := by
        --       simp [lookup]; split; simp_all; apply q3
        --     simp [Option.map, Option.getD] at w4
        --     rw [lem] at w4; simp at w4
        --   case _ => cases w4
      case openm T b y j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih
      case odata y j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih
      case defn T b t' y j1 j2 j3 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j3; injection j3
        case _ e => exact ih
      case inst y T t' j1 j2 => simp [lookup]; exact ih
      case octor y T j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih

theorem lookup_weaken (wf : ⊢ (g::G)) : lookup x G = some e -> lookup x (g::G) = some e := by
  intro h; apply GlobalWf.drop_lookup_unique 1 wf h

theorem lookup_weaken_ctors_vec (wf : ⊢ (Global.data n y D ctors :: G)) (h : x ≠ y)
  : {v : Vec _ k} ->
    lookup x G = some e ->
    (∀ (i : Fin k), v[i] = none) ->
    v.foldl Option.or (lookup x G) = some e
| .nil, h1, h2 => h1
| .cons hd tl, h1, h2 => by
  have h2' := λ (i : Fin _) => h2 (Fin.succ i); simp at h2'
  have lem := lookup_weaken_ctors_vec (v := tl) wf h h1 h2'
  cases hd
  case _ => simp; apply lem
  case _ hd => replace h2 := h2 0; simp at h2

theorem lookup_weaken_ctors (wf : ⊢ (Global.data n y D ctors :: G)) (h : x ≠ y)
  : lookup x (Global.data 0 y D #() :: G) = some e ->
    lookup x (Global.data n y D ctors :: G) = some e
:= by
  intro h
  simp [lookup]; simp [lookup] at h
  split; simp_all
  case _ h1 =>
    split at h; simp_all
    apply lookup_weaken_ctors_vec wf h1 h
    intro i; simp; intro h2
    cases wf; case _ wf gwf =>
    cases gwf; case _ ctors q1 q2 q3 =>
    sorry
    -- simp at h2
    -- generalize zdef : ctors i = z
    -- rcases z with ⟨z, A⟩
    -- rw [zdef] at h2; simp at h2; subst h2
    -- replace q3 := q3 i x A zdef
    -- rcases q3 with ⟨q3, q4, q5⟩
    -- simp_all

theorem lookup_kind_weaken (wf : ⊢ (g::G))
  : lookup_kind G x = some K -> lookup_kind (g::G) x = some K
:= by
  intro h; simp_all [lookup_kind, Option.map]
  generalize zdef : lookup x G = z at *
  generalize wdef : lookup x (g::G) = w at *
  cases z; simp at h; case _ z =>
  cases w
  case _ =>
    simp_all
    replace zdef := lookup_weaken wf zdef
    rw [wdef] at zdef; cases zdef
  case _ w =>
    simp_all
    have lem := lookup_weaken wf zdef
    rw [wdef] at lem; cases lem; exact h

theorem lookup_kind_weaken_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : lookup_kind (Global.data 0 y D #() :: G) x = some K ->
    lookup_kind (Global.data n y D ctors :: G) x = some K
:= by
  intro h1; simp_all [lookup_kind, Option.map]
  generalize zdef : lookup x (Global.data 0 y D #() :: G) = z at *
  generalize wdef : lookup x (Global.data n y D ctors :: G) = w at *
  cases z; simp at h1; case _ z =>
  cases w
  case _ =>
    simp_all; cases String.decEq x y
    case _ lem =>
      replace zdef := lookup_weaken_ctors wf lem zdef
      rw [wdef] at zdef; cases zdef
    case _ lem =>
      subst lem; simp [lookup] at zdef wdef
  case _ w =>
    simp_all; cases String.decEq x y
    case _ lem =>
      have lem := lookup_weaken_ctors wf lem zdef
      rw [wdef] at lem; cases lem; exact h1
    case _ lem =>
      subst lem; simp [lookup] at zdef wdef
      subst zdef wdef; simp_all [Entry.kind]

theorem lookup_ctor_weaken (wf : ⊢ (g::G))
  : lookup_ctor? G c x D -> lookup_ctor? (g::G) c x D
:= by
  intro h; simp_all [lookup_ctor?, Option.map]
  generalize zdef : D.spine = z at *
  cases z; simp_all
  case _ val =>
    rcases val with ⟨z, D⟩
    simp at *
    generalize wdef : lookup x G = w
    cases w; simp_all; case _ e =>
    have lem := lookup_weaken wf wdef
    rw [lem]; simp; rw [wdef] at h; simp at h
    exact h

theorem lookup_ctor_weaken_ctors (wf : ⊢ (Global.data n y K ctors :: G))
  : lookup_ctor? (Global.data 0 y K #() :: G) c x D ->
    lookup_ctor? (Global.data n y K ctors :: G) c x D
:= by
  intro h; simp_all [lookup_ctor?, Option.map]
  generalize zdef : D.spine = z at *
  cases z; simp_all
  case _ val =>
    rcases val with ⟨z, D⟩
    simp at *
    generalize wdef : lookup x (Global.data 0 y K #() :: G) = w at *
    cases w; simp_all; case _ e =>
    cases String.decEq x y
    case _ lem =>
      have lem := lookup_weaken_ctors wf lem wdef
      rw [lem]; simp_all
    case _ lem =>
      subst lem; simp_all [lookup]
      subst wdef; simp_all [Entry.ctor?]

@[simp]
theorem ite_not_resolve [Decidable p] : ¬ p -> ite p a b = b := by
  intro h; split; exfalso; simp_all; rfl

-- theorem lookup_ctor_strengthen_vec (wf : ⊢ (Global.data n d K ctors :: G))

theorem lookup_ctor_strengthen (wf : ⊢ (g::G))
  (hdata : Ty.data? DataConst.cls G D)
  : lookup_ctor? (g::G) .cls x D -> lookup_ctor? G .cls x D
:= by
  sorry
  -- intro h; simp_all [lookup_ctor?]
  -- simp [Ty.data?, Ty.HeadVariable] at hdata
  -- rcases hdata with ⟨y, ⟨z, q1⟩, q2⟩; rw [q1]; rw [q1] at h; simp_all [Option.map]
  -- simp [is_data, Option.map] at q2
  -- have lem1 : ∀ n K ctors, g ≠ .data n x K ctors := by
  --   intro n K ctors h; subst h; simp [lookup, Entry.ctor?] at h
  -- have lem2 : ∀ T, g ≠ .octor x T := by
  --   intro T h; subst h; simp [lookup, Entry.ctor?] at h
  -- cases g <;> simp [lookup] at h
  -- case data w _ ctors =>
  --   cases decEq x w
  --   case _ e =>
  --     rw [ite_not_resolve e] at h
  --     rw [GlobalWf.drop_lookup_unique_vec] at h; apply h
  --     intro i; simp; intro h
  --     cases wf; case _ wf gwf =>
  --     cases gwf; case _ ctors q3 q4 q5 q6 =>
  --     simp at h; generalize zdef : ctors i = z at *
  --     rcases z with ⟨z, C⟩; simp at h; subst h
  --     replace q5 := q5 i x C zdef
  --     rcases q5 with ⟨q5, q7, q8⟩
  --     -- cases q5; case _ R _ _ _ w0 w1 w2 w3 w4 =>
  --     -- replace w3 := w3 .cls rfl
  --     -- simp [lookup_ctor?] at w3
  --     -- generalize Rsdef : R.spine = Rs at *
  --     -- cases Rs; simp at w3; case _ Rs =>
  --     -- rcases Rs with ⟨Rx, RT⟩; simp [Option.map] at w3
  --     -- generalize vdef : lookup y G = v at *
  --     -- cases v; simp_all; case _ ve =>
  --     -- simp [Entry.is_data] at q2
  --     sorry
  --   case _ e =>
  --     subst e; exfalso
  --     apply lem1; rfl
  -- case octor w _ =>
  --   cases decEq x w
  --   case _ e =>
  --     rw [ite_not_resolve e] at h
  --     apply h
  --   case _ e =>
  --     subst e; exfalso
  --     apply lem2; rfl
  -- all_goals split at h <;> simp_all
  -- all_goals case _ e =>
  --   split at e <;> simp_all
  --   subst e; simp_all [Entry.ctor?]

theorem lookup_defn_weaken (wf : ⊢ (g::G))
  : lookup_defn G x = some e -> lookup_defn (g::G) x = some e
:= by
  intro h; simp_all [lookup_defn, Option.bind]
  generalize zdef : lookup x G = z at *
  cases z; simp_all; case _ e =>
  have lem := lookup_weaken wf zdef
  rw [lem]; simp
  cases e <;> simp at *; exact h

theorem lookup_spine_type_weaken (wf : ⊢ (g::G))
  : lookup_spine_type G x = some e -> lookup_spine_type (g::G) x = some e
:= by
  intro h; simp_all [lookup_spine_type, Option.map]
  generalize zdef : lookup x G = z at *
  cases z; simp_all; case _ e =>
  have lem := lookup_weaken wf zdef
  rw [lem]; simp_all

theorem is_data_weaken (wf : ⊢ (g::G)) : is_data c G x -> is_data c (g::G) x := by
  intro h; simp_all [is_data, Option.map]
  generalize zdef : lookup x G = z at *
  cases z; simp_all; case _ e =>
  have lem := lookup_weaken wf zdef
  rw [lem]; simp_all

theorem is_data_weaken_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : is_data c (Global.data 0 y D #() :: G) x -> is_data c (Global.data n y D ctors :: G) x
:= by
  intro h; simp_all [is_data, Option.map]
  generalize zdef : lookup x (Global.data 0 y D #() :: G) = z at *
  cases z; simp_all; case _ e =>
  cases String.decEq x y
  case _ lem =>
    have lem := lookup_weaken_ctors wf lem zdef
    rw [lem]; simp_all
  case _ lem =>
    subst lem; simp_all [lookup, Entry.is_data]
    cases c <;> simp_all
    cases e <;> simp_all

theorem Ty.data?_global_weaken (wf : ⊢ (g::G))
  : Ty.data? c G A -> Ty.data? c (g::G) A
:= by
  sorry
  -- intro h; simp_all [Ty.data?, Ty.HeadVariable]
  -- rcases h with ⟨x, ⟨T, h1⟩, h2⟩
  -- exists x; apply And.intro
  -- exists T; apply is_data_weaken wf h2

theorem Ty.data?_global_weaken_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : Ty.data? c (Global.data 0 y D #() :: G) A -> Ty.data? c (Global.data n y D ctors :: G) A
:= by
  sorry
  -- intro h; simp_all [Ty.data?, Ty.HeadVariable]
  -- rcases h with ⟨x, ⟨T, h1⟩, h2⟩
  -- exists x; apply And.intro
  -- exists T; apply is_data_weaken_ctors wf h2

theorem Kinding.weaken_global (wf : ⊢ (g::G)) : G&Δ ⊢ A : K -> (g::G)&Δ ⊢ A : K
| var h => var h
| global h => global $ lookup_kind_weaken wf h
| arrow j1 j2 => arrow (j1.weaken_global wf) (j2.weaken_global wf)
| all j1 => all (j1.weaken_global wf)
| app j1 j2 => app (j1.weaken_global wf) (j2.weaken_global wf)
| eq j1 j2 => eq (j1.weaken_global wf) (j2.weaken_global wf)

theorem Kinding.weaken_global_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : (Global.data 0 y D #() :: G)&Δ ⊢ A : K -> (Global.data n y D ctors :: G)&Δ ⊢ A : K
| var h => var h
| global h => global $ lookup_kind_weaken_ctors wf h
| arrow j1 j2 => arrow (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)
| all j1 => all (j1.weaken_global_ctors wf)
| app j1 j2 => app (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)
| eq j1 j2 => eq (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)

theorem SpineKinding.weaken_global (wf : ⊢ (g::G))
  : {T : SpineTy} -> SpineKinding v x G tst T -> SpineKinding v x (g::G) tst T
| ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩, valid e j1 j2 j3 j4 =>
  have lem2 : v = .openm → ∀ (i : Fin n), Ty.data? DataConst.opn (g::G) Ts[i] :=
    λ e i => Ty.data?_global_weaken wf (j4 e i)
  valid e (λ i => (j1 i).weaken_global wf) (j2.weaken_global wf) j3 lem2

theorem SpineKinding.weaken_global_ctors (wf : ⊢ (Global.data n y K ctors :: G))
  : SpineKinding v x (Global.data 0 y K #() :: G) tst T ->
    SpineKinding v x (Global.data n y K ctors :: G) tst T
| valid e j1 j2 j3 j4 =>
  let j1' := λ i => (j1 i).weaken_global_ctors wf
  let j2' := j2.weaken_global_ctors wf
  let j4' := λ e i => Ty.data?_global_weaken_ctors wf (j4 e i)
  valid e j1' j2' j3 j4'

theorem PatternBinders.weaken_global (wf : ⊢ (g::G))
  : PatternBinders G Δ m S p ζ ξ -> PatternBinders (g::G) Δ m S p ζ ξ
| zero => zero
| succ j1 j2 e1 e2 e3 j3 =>
  let j1' := lookup_spine_type_weaken wf j1
  let j2' := λ i => (j2 i).weaken_global wf
  let j3' := j3.weaken_global wf
  succ j1' j2' e1 e2 e3 j3'

theorem CoercionProject.weaken_global (wf : ⊢ (g::G))
  : CoercionProject G Δ n T R -> CoercionProject (g::G) Δ n T R
| fst_app j => fst_app (j.weaken_global wf)
| snd_app j => snd_app (j.weaken_global wf)
| fst_arrow j => fst_arrow (j.weaken_global wf)
| snd_arrow j => snd_arrow (j.weaken_global wf)

-- TODO: fix, only try if `g` is not data
theorem Query.global_strengthen {S : Vec _ m} (wf : ⊢ (g::G))
  (h : ∀ (i : Fin m), Ty.data? DataConst.cls G S[i])
  : Query (g::G) .cls q S -> Query G .cls q S
:= by
  intro q
  induction q; apply VecTyping.nil; case _ q S x qs Ss j1 j2 ih =>
  have h' := λ i => h (Fin.succ i); simp at h'
  have lem := h 0; simp at lem
  apply VecTyping.cons _ (ih h')
  apply lookup_ctor_strengthen wf lem j1

theorem Typing.weaken_global (wf : ⊢ (g::G)) : G&Δ,Γ ⊢ t : A -> (g::G)&Δ,Γ ⊢ t : A
| var j1 j2 => var j1 (j2.weaken_global wf)
| defn j1 j2 => defn (lookup_defn_weaken wf j1) (j2.weaken_global wf)
| spctor j1 e1 e2 j2 j3 j4 j5 j6 j7 =>
  sorry
  -- let j1' := lookup_spine_type_weaken wf j1
  -- let j2' := λ i => (j2 i).weaken_global wf
  -- let j3' := λ i => (j3 i).weaken_global wf
  -- let j4' := λ c e => lookup_ctor_weaken wf (j4 c e)
  -- let j5' := λ e i => Ty.data?_global_weaken wf (j5 e i)
  -- spctor j1' e1 e2 j2' j3' j4' j5'
| mtch (m := m) (S := S) j1 j2 j3 j4 j5 =>
  let j1' := λ i => (j1 i).weaken_global wf
  let j2' := λ i => Ty.data?_global_weaken wf (j2 i)
  let j2'' : ∀ (i : Fin m), Ty.data? DataConst.cls G S.to[i] := by sorry
  let j3' := λ i => (j3 i).weaken_global wf
  let j4' := λ i => (j4 i).weaken_global wf
  let j5' := λ {q} q' => j5 (q := q) (Query.global_strengthen wf j2'' q')
  mtch j1' j2' j3' j4' j5'
| lam j1 j2 => lam (j1.weaken_global wf) (j2.weaken_global wf)
| app j1 j2 => app (j1.weaken_global wf) (j2.weaken_global wf)
| lamt j1 j2 => lamt (j1.weaken_global wf) (j2.weaken_global wf)
| appt j1 j2 e => appt (j1.weaken_global wf) (j2.weaken_global wf) e
| refl j1 => refl (j1.weaken_global wf)
| cast j1 j2 j3 e => cast (j1.weaken_global wf) (j2.weaken_global wf) (j3.weaken_global wf) e
| prj j1 j2 => prj (j1.weaken_global wf) (j2.weaken_global wf)
| allc j1 => allc (j1.weaken_global wf)
| apptc j1 j2 e1 e2 => apptc (j1.weaken_global wf) (j2.weaken_global wf) e1 e2

theorem EntryWf.weaken (wf : ⊢ (g::G))
  : EntryWf G e -> EntryWf (g::G) e
| data j => data (lookup_weaken wf j)
| ctor z K ctors i j1 e1 j2 j3 =>
  let j1' := lookup_weaken wf j1
  let j2' := j2.weaken_global wf
  let j3' := lookup_weaken wf j3
  ctor z K ctors i j1' e1 j2' j3'
| odata j => odata (lookup_weaken wf j)
| openm j1 j2 => openm (j1.weaken_global wf) (lookup_weaken wf j2)
| defn j1 j2 j3 => defn (j1.weaken_global wf) (j2.weaken_global wf) (lookup_weaken wf j3)
| octor j1 j2 => sorry -- octor (j1.weaken_global wf) (lookup_weaken wf j2)

theorem EntryWf.from_lookup_ctor1 :
  {v : Vec _ n} ->
  v.foldl Option.or (lookup x G) = some e ->
  lookup x G = some e ∨ (∃ (i : Fin n), v[i] = some e)
| .nil, eq => Or.inl eq
| .cons a tl, eq => by
  sorry
  -- simp at eq; cases eq
  -- case _ eq => apply Or.inr; exists 0
  -- case _ eq =>
  --   have lem := from_lookup_ctor1 eq.2
  --   cases lem
  --   case _ lem => apply Or.inl lem
  --   case _ lem =>
  --     rcases lem with ⟨i, lem⟩
  --     apply Or.inr; exists (Fin.succ i)

-- TODO: need decidable equality of Entry
theorem EntryWf.from_lookup_ctor2 :
  {v : Vec (Option Entry) n} ->
  (∃ (i : Fin n), v[i].isSome) ->
  v.foldl Option.or none = some e
| .nil, ⟨i, h⟩ => Fin.elim0 i
| .cons a tl, ⟨i, h⟩ => by
  sorry
  -- cases i using Fin.cases
  -- case zero => sorry
  -- case succ i =>
  --   simp at h; simp
  --   apply Or.inr
  --   have lem := EntryWf.from_lookup_ctor2 (e := e) (v := tl) ⟨i, h⟩
  --   sorry

theorem EntryWf.from_lookup :
  ⊢ G ->
  lookup x G = some e ->
  EntryWf G e
:= by
  intro wf h
  fun_induction lookup
  any_goals try
    case _ ih =>
      cases wf; case _ h2 wf =>
      apply weaken
      apply ListGlobalWf.cons wf h2
      apply ih h2 h
  case _ => cases h
  case _ =>
    cases h; apply EntryWf.data
    simp [lookup]
  case _ n y K ctors tl ctors' h1 ih1 =>
    sorry
    -- have wf' := wf
    -- cases wf; case _ wf gwf =>
    -- cases gwf; case _ ctors2 h2 h3 h4 =>
    -- cases (EntryWf.from_lookup_ctor1 h)
    -- case _ lem => apply EntryWf.weaken wf' (ih1 wf lem)
    -- case _ lem =>
    --   rcases lem with ⟨i, lem⟩
    --   clear h; subst ctors'; simp at lem
    --   generalize zdef : ctors2 i = z
    --   rcases z with ⟨z, A⟩
    --   replace h4 := h4 i z A zdef
    --   rw [zdef] at lem; simp at lem
    --   rcases h4 with ⟨q1, q2, q3⟩
    --   rw [<-lem.2]; apply EntryWf.ctor y K ctors2
    --   simp [lookup]
    --   simp; exact zdef
    --   apply SpineKinding.weaken_global_ctors wf' q1
    --   simp [lookup]; split; simp_all; rw [q3]
    --   apply EntryWf.from_lookup_ctor2; simp
    --   exists i; rw [zdef]
      -- apply EntryWf.from_lookup_ctor3; simp
      -- exists i; rw [zdef]; simp
  case _ =>
    cases h; apply EntryWf.odata
    simp [lookup]
  case _ =>
    have wf' := wf
    cases h; cases wf; case _ wf h =>
    cases h; case _ j1 j2 =>
    apply EntryWf.openm
    apply SpineKinding.weaken_global wf' j2
    simp [lookup]
  case _ =>
    have wf' := wf
    cases h; cases wf; case _ wf h =>
    cases h; case _ j1 j2 =>
    apply EntryWf.defn
    apply Kinding.weaken_global wf' j1
    apply Typing.weaken_global wf' j2
    simp [lookup]
  case _ =>
    sorry
    -- have wf' := wf
    -- cases h; cases wf; case _ wf h =>
    -- cases h; case _ j1 j2 =>
    -- apply EntryWf.octor
    -- apply SpineKinding.weaken_global wf' j2
    -- simp [lookup]

theorem EntryWf.from_lookup_defn :
  ⊢ G ->
  lookup_defn G x = some ⟨t, T⟩ ->
  EntryWf G (.defn x t T)
:= by
  intro h1 h2
  simp [lookup_defn, Option.bind] at h2
  generalize zdef : lookup x G = z at *
  cases z; simp_all; case _ e =>
  have lem := EntryWf.from_lookup h1 zdef
  simp at h2; cases e <;> simp at h2
  rcases h2 with ⟨e1, e2⟩; subst e1 e2
  have lem2 := lookup_name_agrees zdef
  simp [Entry.name] at lem2; subst lem2
  apply lem

theorem GlobalWf.index_instance {i : Nat} :
  ⊢ G ->
  G[i]? = some (.inst x p b) ->
  GlobalWf G (.inst x p b)
:= by
  intro wf h2
  induction G generalizing i; simp at h2
  case _ hd tl ih =>
    cases i <;> simp at h2
    case _ =>
      subst h2; cases wf; case _ wf gwf =>
      have gwf' := gwf
      cases gwf; case _ e _ j1 j2 j3 =>
      have wf' := ListGlobalWf.cons gwf' wf
      apply GlobalWf.inst
      apply lookup_weaken wf' j1
      apply e
      apply PatternBinders.weaken_global wf' j2
      apply Typing.weaken_global wf' j3
    case _ =>
      cases wf; case _ wf gwf =>
      replace ih := ih wf h2
      cases ih; case _ e _ j1 j2 j3 =>
      have wf' := ListGlobalWf.cons gwf wf
      apply GlobalWf.inst
      apply lookup_weaken wf' j1
      apply e
      apply PatternBinders.weaken_global wf' j2
      apply Typing.weaken_global wf' j3

-- theorem EntryWf.get_openm {G} {Δ} {Γ} :
--   ⊢ G ->
--   EntryWf G (.openm x T) ->
--   G&Δ, Γ  ⊢ g#x : T ∧
--   ∃ b, G&Δ ⊢ T : .base b
-- := by
--   intro wf e; cases e; case _ b j1 j2 =>
--   apply And.intro
--   apply Typing.global; simp [lookup_type]; rw [j2]; simp
--   simp [Entry.type]
--   apply Kinding.closed_arbitrary_weakening Δ wf j1
--   exists b; apply Kinding.closed_arbitrary_weakening Δ wf j1

-- theorem GlobalWf.types_have_base_kind :
--   ⊢ G ->
--   lookup_type G x = some T ->
--   ∃ b, G&Δ ⊢ T : .base b
-- := by
--   intro wf h
--   simp [lookup_type] at h
--   generalize zdef : lookup x G = z at h
--   cases z; simp at h; case _ z =>
--   have lem := EntryWf.from_lookup wf zdef
--   cases lem <;> simp [Entry.type] at h
--   case ctor j1 j2 j3 j4 j5 =>
--     apply Exists.intro _; subst h
--     apply Kinding.closed_arbitrary_weakening Δ wf j4
--   case openm j1 j2 =>
--     apply Exists.intro _; subst h
--     apply Kinding.closed_arbitrary_weakening Δ wf j1
--   case defn j1 j2 j3 =>
--     apply Exists.intro _; subst h
--     apply Kinding.closed_arbitrary_weakening Δ wf j1
--   case instty j1 j2 =>
--     obtain ⟨b, lem⟩ := ValidInstTy.closed j1
--     subst h; exists b
--     apply Kinding.closed_arbitrary_weakening Δ wf lem

-- theorem GlobalWf.lookup_type_sound :
--   ⊢ G ->
--   lookup_type G x = some T ->
--   G&Δ,Γ ⊢ g#x : T := by
--  intro wf h
--  have lem := GlobalWf.types_have_base_kind (Δ := Δ) wf h;
--  rcases lem with ⟨bk, lem⟩
--  constructor; assumption;
--  apply lem;

-- theorem GlobalWf.lookup_defn_type_exists {G : List Global} {Δ : List Kind} :
--   ⊢ G ->
--   lookup_defn G x = some t ->
--   ∃ T b, lookup_type G x = some T ∧ G&Δ ⊢ T : .base b
-- := by
--   intro wf h
--   unfold lookup_defn at h; simp at h
--   obtain ⟨w, q1, q2⟩ := Option.bind_eq_some_iff.1 h; clear h
--   cases w <;> simp at q2; case _ y A t' =>
--   subst q2
--   have lem : lookup_type G x = some A := by
--     simp [lookup_type]; rw [q1]; simp [Entry.type]
--   obtain ⟨b, h⟩ := types_have_base_kind (Δ := Δ) wf lem
--   exists A; exists b

-- theorem GlobalWf.lookup_defn_type {G : List Global} {Δ : List Kind} {Γ : List Ty} :
--   ⊢ G ->
--   lookup_defn G x = some t ->
--   ∃ T b, G&Δ,Γ ⊢ g#x : T ∧ G&Δ,Γ ⊢ t : T ∧ G&Δ ⊢ T : .base b
-- := by
--   intro wf j
--   unfold lookup_defn at j; simp at j
--   obtain ⟨a, j1, j2⟩ := Option.bind_eq_some_iff.1 j; clear j
--   have lem := EntryWf.from_lookup wf j1
--   cases lem <;> simp at j2
--   case _ T b t y q1 q2 q3 =>
--   subst j2; exists T; exists b; apply And.intro
--   apply Typing.global; simp [lookup_type]; rw [j1]; simp [Entry.type]
--   apply Kinding.closed_arbitrary_weakening Δ wf q1
--   apply And.intro
--   replace q2 := Typing.weaken_type_closed Δ wf q2
--   apply Typing.weaken_closed Γ wf q2
--   apply Kinding.closed_arbitrary_weakening Δ wf q1

end Core
