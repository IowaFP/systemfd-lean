import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

import Core.Metatheory.Substitution
import Core.Metatheory.Rename
import Core.Global

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
  (∀ i, v i = none) ->
  Vec.fold Option.or (lookup x G) v = lookup x G
:= by
  intro h
  induction v using Vec.induction
  case _ => simp
  case _ hd tl ih =>
    simp; have lem := h 0; simp at lem
    subst lem; simp
    rw [ih]; intro i
    apply h (Fin.succ i)

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
      case data n y K ctors ctors' j1 j2 j3 j4 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j4; injection j4
        case _ e =>
          rw [drop_lookup_unique_vec]; exact ih
          intro i
          generalize endef : ctors i = en at *
          rcases en with ⟨z, A⟩; simp; intro e2; subst e2
          replace j3 := j3 i x A endef
          rcases j3 with ⟨j3, j4, j5⟩
          simp [lookup] at j5; split at j5
          case _ e2 => apply e e2
          case _ e2 => rw [ih] at j5; injection j5
      case openm T b y j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih
      case opent y j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih
      case defn T b t' y j1 j2 j3 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j3; injection j3
        case _ e => exact ih
      case inst y T t' j1 j2 => simp [lookup]; exact ih
      case instty y T j1 j2 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j2; injection j2
        case _ e => exact ih

theorem GlobalWf.drop_lookup_impossible {G : List Global} :
  ⊢ G ->
  G' = G.drop n ->
  lookup x G' = some t ->
  lookup x G = none ->
  False
:= by
  intro wf e h1 h2
  subst e; replace h1 := drop_lookup_unique n wf h1
  rw [h2] at h1; injection h1

theorem GlobalWf.drop_lookup {G : List Global} n :
  ⊢ G ->
  G' = G.drop n ->
  lookup x G' = some t ->
  lookup x G = some t' ->
  t = t'
:= by
  intro wf e h1 h2
  subst e; replace h1 := drop_lookup_unique n wf h1
  have lem := Global.lookup_unique h1 h2
  injection lem

theorem Kinding.drop_weaken_global n :
  ⊢ G ->
  G' = G.drop n ->
  G'& Δ ⊢ T : K ->
  G&Δ ⊢ T : K
:= by
  intro wf e j
  induction j generalizing G
  case var =>
    apply Kinding.var; assumption
  case global x K Δ h =>
    apply Kinding.global
    simp [lookup_kind] at *;
    generalize zdef  : lookup x G = z at *
    generalize zdef' : lookup x G' = z' at *
    cases z'; simp at h; case _ z' =>
    cases z; simp at h
    case none =>
      exfalso
      apply GlobalWf.drop_lookup_impossible wf e zdef' zdef
    case some z =>
      have lem := GlobalWf.drop_lookup n wf e zdef' zdef
      subst z'; assumption
  case all j ih =>
    replace ih := @ih G wf e
    apply Kinding.all; assumption
  all_goals (case _ ih1 ih2 =>
    replace ih1 := @ih1 G wf e
    replace ih2 := @ih2 G wf e
    constructor; assumption; assumption)

theorem Typing.drop_weaken_global n :
  ⊢ G ->
  G' = G.drop n ->
  G'&Δ,Γ ⊢ t : T ->
  G&Δ,Γ ⊢ t : T
:= by
  intro wf e j
  induction j generalizing G
  case var => sorry
  case global x A Δ b Γ j1 j2 =>
    sorry
    -- apply global; simp [lookup_type] at *
    -- generalize zdef  : lookup x G = z at *
    -- generalize zdef' : lookup x G' = z' at *
    -- have lem := GlobalWf.drop_lookup n wf e zdef' zdef
    -- subst z'; rw [lem] at j1; exact j1
    -- apply Kinding.drop_weaken_global n wf e j2
  case mtch => sorry
  case guard => sorry
  case lam => sorry
  case app => sorry
  case lamt => sorry
  case appt => sorry
  case cast => sorry
  case refl => sorry
  case sym => sorry
  case seq => sorry
  case appc => sorry
  case arrowc => sorry
  case fst => sorry
  case snd => sorry
  case allc => sorry
  case apptc => sorry
  case zero j =>
    apply zero
    apply Kinding.drop_weaken_global n wf e j
  case choice => sorry

theorem ValidInstTy.drop_weaken_global n :
  ⊢ G ->
  G' = G.drop n ->
  ValidInstTy G' x Δ A ->
  ValidInstTy G x Δ A
:= by
  intro wf e j
  induction j generalizing G
  case base j1 j2 =>
    apply ValidInstTy.base j1
    apply Kinding.drop_weaken_global n wf e j2
  case all j1 j2 ih =>
    apply ValidInstTy.all
    apply Kinding.drop_weaken_global n wf e j1
    apply ih wf e
  case arrow j1 j2 ih =>
    apply ValidInstTy.arrow
    apply ih wf e
    apply Kinding.drop_weaken_global n wf e j2

theorem GlobalWf.lookup_weaken :
  ⊢ (e1::G) ->
  lookup x G = some e2 ->
  lookup x (e1::G) = some e2
:= by
  intro wf j
  apply drop_lookup_unique 1 wf
  simp; exact j

theorem EntryWf.weaken :
  ⊢ (e1::G) ->
  EntryWf G e2 ->
  EntryWf (e1::G) e2
:= by
  intro wf j
  induction j
  case data j =>
    apply EntryWf.data
    apply GlobalWf.lookup_weaken wf j
  case ctor j1 j2 j3 =>
    apply EntryWf.ctor
    apply Kinding.drop_weaken_global 1 wf (by simp) j1
    apply j2
    apply GlobalWf.lookup_weaken wf j3
  case opent j1 j2 =>
    apply EntryWf.opent j1
    apply GlobalWf.lookup_weaken wf j2
  case openm j1 j2 =>
    apply EntryWf.openm
    apply Kinding.drop_weaken_global 1 wf (by simp) j1
    apply GlobalWf.lookup_weaken wf j2
  case defn j1 j2 j3 j4 =>
    apply EntryWf.defn
    apply Kinding.drop_weaken_global 1 wf (by simp) j2
    apply Typing.drop_weaken_global 1 wf (by simp) j3
    apply GlobalWf.lookup_weaken wf j4
  case instty j1 j2 =>
    apply EntryWf.instty
    apply ValidInstTy.drop_weaken_global 1 wf (by simp) j1
    apply GlobalWf.lookup_weaken wf j2

theorem EntryWf.from_lookup :
  ⊢ G ->
  lookup x G = some e ->
  EntryWf G e
:= by
  intro wf h
  induction wf generalizing e
  case nil => simp [lookup] at h
  case cons G g gwf wf ih =>
    have gwf' := gwf
    have wf' := ListGlobalWf.cons gwf' wf
    cases gwf <;> simp [lookup] at h
    case data j1 j2 j3 j4 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.data; simp [lookup]
      case _ e1 =>

        sorry
    case opent j1 j2 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.opent j1; simp [lookup]
      case _ e1 => apply weaken wf' (ih h)
    case openm j1 j2 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.openm
        apply Kinding.drop_weaken_global 1 wf' (by simp) j1
        simp [lookup]
      case _ e1 => apply weaken wf' (ih h)
    case defn j1 j2 j3 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.defn
        apply Kinding.drop_weaken_global 1 wf' (by simp) j1
        apply Typing.drop_weaken_global 1 wf' (by simp) j2
        simp [lookup]
      case _ e1 => apply weaken wf' (ih h)
    case inst j1 j2 =>

      sorry
    case instty j1 j2 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.instty
        apply ValidInstTy.drop_weaken_global 1 wf' (by simp) j1
        simp [lookup]
      case _ e1 => apply weaken wf' (ih h)

theorem EntryWf.get_openm {G} {Δ} {Γ} :
   ⊢ G ->
   EntryWf G (.openm x T) ->
   G&Δ, Γ  ⊢ g#x : T ∧
   ∃ b, G&Δ ⊢ T : .base b := by
intro wf h; cases h; case _ h =>
rcases h with ⟨n, p, h1, h2⟩
cases h2; case _ bk _ j =>
have lem := Kinding.closed_arbitrary_weakening (Δ' := Δ) (GlobalWf.drop_wf _ wf) j
generalize gdef : G.drop n = G' at *; symm at gdef
have lem := Kinding.arbitrary_weakening_global wf gdef lem
constructor
· apply Typing.global;
  assumption; assumption
· exists bk

theorem GlobalWf.types_have_base_kind :
  ⊢ G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢ T : .base b
:= by
  intro wf h
  -- generalize lkdef : lookup_type G x = lk at *
  induction wf generalizing x T
  case _ => simp [lookup_type, lookup, default] at *
  case _ G g gwf wf ih =>
    replace ih := @ih x T
    have gwf' := gwf
    cases gwf <;> simp [lookup_type, lookup] at h
    case data => sorry
    case opent K y h1 h2 =>
      replace h := get!_option2_eq_some h
      obtain ⟨w, q1, q2⟩ := Option.map_eq_some_iff.1 h
      clear h; split at q1
      case _ e =>
        subst e; injection q1 with e; subst e
        simp [Entry.type] at q2
      case _ e =>
        have lem := lookup_type_reconstruct q1 q2
        obtain ⟨b, ih⟩ := ih lem
        exists b; apply Kinding.arbitrary_weakening_global (n := 1) _ (by simp) ih
        apply ListGlobalWf.cons gwf' wf
    case openm => sorry
    case defn => sorry
    case inst => sorry
    case instty =>
      sorry

theorem GlobalWf.lookup_type_sound :
  ⊢ G ->
  lookup_type G x = some T ->
  G&Δ,Γ ⊢ g#x : T := by
 intro wf h
 have lem := GlobalWf.types_have_base_kind (Δ := Δ) wf h;
 rcases lem with ⟨bk, lem⟩
 constructor; assumption;
 apply lem;

theorem GlobalWf.lookup_defn_type_exists {G : List Global} {Δ : List Kind} {Γ : List Ty} :
  ⊢ G ->
  lookup_defn G x = some t ->
  ∃ T b, lookup_type G x = some T ∧ G&Δ ⊢ T : .base b
:= by
  intro wf h
  unfold lookup_defn at h; simp at h
  obtain ⟨w, q1, q2⟩ := Option.bind_eq_some_iff.1 h; clear h
  cases w <;> simp at q2; case _ y A t' =>
  subst q2
  have lem : lookup_type G x = some A := by
    simp [lookup_type]; rw [q1]; simp [Entry.type]
  obtain ⟨b, h⟩ := types_have_base_kind (Δ := Δ) wf lem
  exists A; exists b

theorem GlobalWf.lookup_defn_type {G : List Global} {Δ : List Kind} {Γ : List Ty} :
  ⊢ G ->
  lookup_defn G x = some t ->
  ∃ T b, G&Δ, Γ ⊢ g#x : T ∧ G&Δ, Γ ⊢ t : T ∧ G&Δ ⊢ T : .base b := by
intro wf h1
have lem := GlobalWf.lookup_defn_type_exists (G := G) (Δ := Δ) (Γ := Γ) wf h1
rcases lem with ⟨T, b, lem1, lem2⟩
exists T; exists b
constructor
· apply lookup_type_sound wf lem1
· sorry

end Core
