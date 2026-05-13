
import Core.Vec
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Global

open Lilac

namespace Core

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
  Vec.fold (lookup x G) Option.or v = lookup x G
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
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j3; injection j3
        case _ e =>
          rw [drop_lookup_unique_vec]; exact ih
          intro i
          generalize endef : ctors i = en at *
          rcases en with ⟨z, A⟩; simp; intro e2
          replace j2 := j2 i z A endef
          rcases j2 with ⟨q1, q2, q3⟩
          cases q1; case _ w1 w2 w3 w4 w5 =>
          clear w5; replace w4 := w4 _ rfl
          simp [lookup_ctor?] at w4; split at w4
          case _ =>
            have lem : lookup z (Global.data 0 y K #𝓋[] :: G) = none := by
              simp [lookup]; split; simp_all; apply q3
            simp [Option.map, Option.getD] at w4
            rw [lem] at w4; simp at w4
          case _ => cases w4
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

-- theorem GlobalWf.drop_lookup_impossible {G : List Global} :
--   ⊢ G ->
--   G' = G.drop n ->
--   lookup x G' = some t ->
--   lookup x G = none ->
--   False
-- := by
--   intro wf e h1 h2
--   subst e; replace h1 := drop_lookup_unique n wf h1
--   rw [h2] at h1; injection h1

-- theorem GlobalWf.drop_lookup {G : List Global} n :
--   ⊢ G ->
--   G' = G.drop n ->
--   lookup x G' = some t ->
--   lookup x G = some t' ->
--   t = t'
-- := by
--   sorry
--   -- intro wf e h1 h2
--   -- subst e; replace h1 := drop_lookup_unique n wf h1
--   -- have lem := Global.lookup_unique h1 h2
--   -- injection lem

-- theorem Kinding.drop_weaken_global n :
--   ⊢ G ->
--   G' = G.drop n ->
--   G'& Δ ⊢ T : K ->
--   G&Δ ⊢ T : K
-- := by
--   intro wf e j
--   induction j generalizing G
--   case var =>
--     apply Kinding.var; assumption
--   case global x K Δ h =>
--     apply Kinding.global
--     simp [lookup_kind] at *;
--     generalize zdef  : lookup x G = z at *
--     generalize zdef' : lookup x G' = z' at *
--     cases z'; simp at h; case _ z' =>
--     cases z; simp at h
--     case none =>
--       exfalso
--       apply GlobalWf.drop_lookup_impossible wf e zdef' zdef
--     case some z =>
--       have lem := GlobalWf.drop_lookup n wf e zdef' zdef
--       subst z'; assumption
--   case all j ih =>
--     replace ih := @ih G wf e
--     apply Kinding.all; assumption
--   all_goals (case _ ih1 ih2 =>
--     replace ih1 := @ih1 G wf e
--     replace ih2 := @ih2 G wf e
--     constructor; assumption; assumption)

-- theorem GlobalWf.drop_weaken_global_lookup_map (f : Entry -> Bool) n :
--   ⊢ G ->
--   G' = G.drop n ->
--   (Option.map f (lookup x G')).get! ->
--   (Option.map f (lookup x G)).get!
-- := by
--   intro wf e j
--   generalize zpdef : lookup x G' = z' at *
--   generalize zdef : lookup x G = z at *
--   cases z' <;> simp at j; case _ z' =>
--   cases z
--   case none =>
--     have lem := GlobalWf.drop_lookup_impossible wf e zpdef zdef
--     cases lem
--   case some z =>
--     have lem := GlobalWf.drop_lookup n wf e zpdef zdef; subst lem
--     simp; exact j

theorem lookup_weaken (wf : ⊢ (g::G)) : lookup x G = some e -> lookup x (g::G) = some e := by
  intro h; apply GlobalWf.drop_lookup_unique 1 wf h

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
  : lookup_kind (Global.data 0 y D #𝓋[] :: G) x = some K ->
    lookup_kind (Global.data n y D ctors :: G) x = some K
:= by
  sorry

theorem lookup_ctor_weaken (wf : ⊢ (g::G))
  : lookup_ctor? G c x D -> lookup_ctor? (g::G) c x D
:= by sorry

theorem lookup_ctor_weaken_ctors (wf : ⊢ (Global.data n y K ctors :: G))
  : lookup_ctor? (Global.data 0 y K #𝓋[] :: G) c x D ->
    lookup_ctor? (Global.data n y K ctors :: G) c x D
:= by sorry

theorem lookup_ctor_strengthen (wf : ⊢ (g::G))
  : lookup_ctor? (g::G) c x D -> lookup_ctor? G c x D
:= by sorry

theorem lookup_defn_weaken (wf : ⊢ (g::G))
  : lookup_defn G x = some e -> lookup_defn (g::G) x = some e
:= by sorry

theorem lookup_spine_type_weaken (wf : ⊢ (g::G))
  : lookup_spine_type G x = some e -> lookup_spine_type (g::G) x = some e
:= by sorry

theorem Ty.data?_global_weaken (wf : ⊢ (g::G))
  : Ty.data? c G A -> Ty.data? c (g::G) A
:= by sorry

theorem Ty.data?_global_weaken_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : Ty.data? c (Global.data 0 y D #𝓋[] :: G) A -> Ty.data? c (Global.data n y D ctors :: G) A
:= by sorry

theorem Kinding.weaken_global (wf : ⊢ (g::G)) : G&Δ ⊢ A : K -> (g::G)&Δ ⊢ A : K
| var h => var h
| global h => global $ lookup_kind_weaken wf h
| arrow j1 j2 => arrow (j1.weaken_global wf) (j2.weaken_global wf)
| all j1 => all (j1.weaken_global wf)
| app j1 j2 => app (j1.weaken_global wf) (j2.weaken_global wf)
| eq j1 j2 => eq (j1.weaken_global wf) (j2.weaken_global wf)

theorem Kinding.weaken_global_ctors (wf : ⊢ (Global.data n y D ctors :: G))
  : (Global.data 0 y D #𝓋[] :: G)&Δ ⊢ A : K -> (Global.data n y D ctors :: G)&Δ ⊢ A : K
| var h => var h
| global h => global $ lookup_kind_weaken_ctors wf h
| arrow j1 j2 => arrow (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)
| all j1 => all (j1.weaken_global_ctors wf)
| app j1 j2 => app (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)
| eq j1 j2 => eq (j1.weaken_global_ctors wf) (j2.weaken_global_ctors wf)

theorem SpineKinding.weaken_global (wf : ⊢ (g::G))
  : {T : SpineTy} -> SpineKinding v x G T -> SpineKinding v x (g::G) T
| ⟨m, Ks, n, Ts, R⟩, valid (τ := τ) e j1 j2 j3 j4 =>
  have lem1 : ∀ c, v = .data c → lookup_ctor? (g::G) c x R :=
    λ c e => lookup_ctor_weaken wf (j3 c e)
  have lem2 : v = .openm → ∀ (i : Fin n), Ty.data? DataConst.opn (g::G) Ts[i][τ] :=
    λ e i => Ty.data?_global_weaken wf (j4 e i)
  valid e (λ i => (j1 i).weaken_global wf) (j2.weaken_global wf) lem1 lem2

theorem SpineKinding.weaken_global_ctors (wf : ⊢ (Global.data n y K ctors :: G))
  : {T : SpineTy} ->
    SpineKinding v x (Global.data 0 y K #𝓋[] :: G) T ->
    SpineKinding v x (Global.data n y K ctors :: G) T
| ⟨m, Ks, n, Ts, R⟩, valid (τ := τ) e j1 j2 j3 j4 => sorry

theorem PatternBinders.weaken_global (wf : ⊢ (g::G))
  : PatternBinders G Δ m S p ξ -> PatternBinders (g::G) Δ m S p ξ
| zero => zero
| succ j1 j2 e1 e2 e3 j4 =>
  let j1' := lookup_spine_type_weaken wf j1
  let j2' := λ i => (j2 i).weaken_global wf
  let j4' := j4.weaken_global wf
  succ j1' j2' e1 e2 e3 j4'

theorem CoercionProject.weaken_global (wf : ⊢ (g::G))
  : CoercionProject G Δ n T R -> CoercionProject (g::G) Δ n T R
| fst_app j => fst_app (j.weaken_global wf)
| snd_app j => snd_app (j.weaken_global wf)
| fst_arrow j => fst_arrow (j.weaken_global wf)
| snd_arrow j => snd_arrow (j.weaken_global wf)

-- TODO: fix, only try if `g` is not data
theorem Query.global_strengthen (wf : ⊢ (g::G))
  : Query (g::G) .cls q S -> Query G .cls q S
:= sorry

theorem Typing.weaken_global (wf : ⊢ (g::G)) : G&Δ,Γ ⊢ t : A -> (g::G)&Δ,Γ ⊢ t : A
| var j1 j2 => var j1 (j2.weaken_global wf)
| defn j1 j2 => defn (lookup_defn_weaken wf j1) (j2.weaken_global wf)
| spctor e1 j1 e2 j2 j3 j4 e3 =>
  let e1' := lookup_spine_type_weaken wf e1
  let j1' := λ i => (j1 i).weaken_global wf
  let j2' := λ i => (j2 i).weaken_global wf
  let j3' := λ c e => lookup_ctor_weaken wf (j3 c e)
  let j4' := λ e i => Ty.data?_global_weaken wf (j4 e i)
  spctor e1' j1' e2 j2' j3' j4' e3
| mtch j1 j2 j3 j4 j5 =>
  let j1' := λ i => (j1 i).weaken_global wf
  let j2' := λ i => Ty.data?_global_weaken wf (j2 i)
  let j3' := λ i => (j3 i).weaken_global wf
  let j4' := λ i => (j4 i).weaken_global wf
  let j5' := λ {q} q' => j5 (q := q) (Query.global_strengthen wf q')
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
| octor j1 j2 => octor (j1.weaken_global wf) (lookup_weaken wf j2)

theorem EntryWf.from_lookup_ctor1 :
  {v : Vec _ n} ->
  Vec.fold (lookup x G) Option.or v = some e ->
  lookup x G = some e ∨ (∃ (i : Fin n), v[i] = some e)
| .nil, eq => Or.inl eq
| .cons a tl, eq => by
  simp at eq; cases eq
  case _ eq => apply Or.inr; exists 0
  case _ eq =>
    have lem := from_lookup_ctor1 eq.2
    cases lem
    case _ lem => apply Or.inl lem
    case _ lem =>
      rcases lem with ⟨i, lem⟩
      apply Or.inr; exists (Fin.succ i)

-- TODO: need decidable equality of Entry
theorem EntryWf.from_lookup_ctor2 :
  {v : Vec (Option Entry) n} ->
  (∃ (i : Fin n), v[i].isSome) ->
  Vec.fold none Option.or v = some e
| .nil, ⟨i, h⟩ => Fin.elim0 i
| .cons a tl, ⟨i, h⟩ => by
  cases i using Fin.cases
  case zero => sorry
  case succ i =>
    simp at h; simp
    apply Or.inr
    have lem := EntryWf.from_lookup_ctor2 (e := e) (v := tl) ⟨i, h⟩
    sorry

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
    have wf' := wf
    cases wf; case _ wf gwf =>
    cases gwf; case _ ctors2 h2 h3 h4 =>
    cases (EntryWf.from_lookup_ctor1 h)
    case _ lem => apply EntryWf.weaken wf' (ih1 wf lem)
    case _ lem =>
      rcases lem with ⟨i, lem⟩
      clear h; subst ctors'; simp at lem
      generalize zdef : ctors2 i = z
      rcases z with ⟨z, A⟩
      replace h4 := h4 i z A zdef
      rw [zdef] at lem; simp at lem
      rcases h4 with ⟨q1, q2, q3⟩
      rw [<-lem.2]; apply EntryWf.ctor y K ctors2
      simp [lookup]
      simp; exact zdef
      apply SpineKinding.weaken_global_ctors wf' q1
      simp [lookup]; split; simp_all; rw [q3]
      apply EntryWf.from_lookup_ctor2; simp
      exists i; rw [zdef]
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
    have wf' := wf
    cases h; cases wf; case _ wf h =>
    cases h; case _ j1 j2 =>
    apply EntryWf.octor
    apply SpineKinding.weaken_global wf' j2
    simp [lookup]

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
