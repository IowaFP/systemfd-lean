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
  Vect.fold (lookup x G) Option.or v = lookup x G
:= by
  intro h
  induction v using Vect.induction
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
      case data n y K ctors j1 j2 j3 =>
        simp [lookup]; split
        case _ e => subst e; rw [ih] at j3; injection j3
        case _ e =>
          rw [drop_lookup_unique_vec]; exact ih
          intro i
          generalize endef : ctors i = en at *
          rcases en with ⟨z, A⟩; simp; intro e2; subst e2
          replace j2 := j2 i x A endef
          rcases j2 with ⟨q1, q2, q3, q4⟩
          rw [ih] at q4; injection q4
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

theorem GlobalWf.drop_weaken_global_lookup_map (f : Entry -> Bool) n :
  ⊢ G ->
  G' = G.drop n ->
  (Option.map f (lookup x G')).get! ->
  (Option.map f (lookup x G)).get!
:= by
  intro wf e j
  generalize zpdef : lookup x G' = z' at *
  generalize zdef : lookup x G = z at *
  cases z' <;> simp at j; case _ z' =>
  cases z
  case none =>
    have lem := GlobalWf.drop_lookup_impossible wf e zpdef zdef
    cases lem
  case some z =>
    have lem := GlobalWf.drop_lookup n wf e zpdef zdef; subst lem
    simp; exact j

theorem ValidTyHeadVariable.drop_weaken_global_is_data n :
  ⊢ G ->
  G' = G.drop n ->
  ValidTyHeadVariable R (is_data G') ->
  ValidTyHeadVariable R (is_data G)
:= by
  intro wf e j
  unfold ValidTyHeadVariable at *
  obtain ⟨x, h1, h2⟩ := j
  unfold is_data at *
  have lem := GlobalWf.drop_weaken_global_lookup_map Entry.is_data n wf e h2
  exists x

theorem ValidTyHeadVariable.drop_weaken_global_is_opent n :
  ⊢ G ->
  G' = G.drop n ->
  ValidTyHeadVariable R (is_opent G') ->
  ValidTyHeadVariable R (is_opent G)
:= by
  intro wf e j
  unfold ValidTyHeadVariable at *
  obtain ⟨x, h1, h2⟩ := j
  unfold is_opent at *
  have lem := GlobalWf.drop_weaken_global_lookup_map Entry.is_opent n wf e h2
  exists x

theorem ValidHeadVariable.drop_weaken_global_is_ctor n :
  ⊢ G ->
  G' = G.drop n ->
  ValidHeadVariable T (is_ctor G') ->
  ValidHeadVariable T (is_ctor G)
:= by
  intro wf e j
  unfold ValidHeadVariable at *
  obtain ⟨x, h1, h2⟩ := j
  unfold is_ctor at *
  have lem := GlobalWf.drop_weaken_global_lookup_map Entry.is_ctor n wf e h2
  exists x

theorem ValidHeadVariable.drop_weaken_global_is_instty n :
  ⊢ G ->
  G' = G.drop n ->
  ValidHeadVariable T (is_instty G') ->
  ValidHeadVariable T (is_instty G)
:= by
  intro wf e j
  unfold ValidHeadVariable at *
  obtain ⟨x, h1, h2⟩ := j
  unfold is_instty at *
  have lem := GlobalWf.drop_weaken_global_lookup_map Entry.is_instty n wf e h2
  exists x

theorem Typing.drop_weaken_global n :
  ⊢ G ->
  G' = G.drop n ->
  G'&Δ,Γ ⊢ t : T ->
  G&Δ,Γ ⊢ t : T
:= by
  intro wf e j
  induction j generalizing G
  case var j1 j2 =>
    apply var j1
    apply Kinding.drop_weaken_global n wf e j2
  case global x A Δ b Γ j1 j2 =>
    apply global _
    apply Kinding.drop_weaken_global n wf e j2
    simp [lookup_type] at *
    generalize zdef  : lookup x G = z at *
    generalize zdef' : lookup x G' = z' at *
    cases z'; simp at j1; case _ z' =>
    cases z; simp at j1
    case none =>
      exfalso
      apply GlobalWf.drop_lookup_impossible wf e zdef' zdef
    case some z =>
      have lem := GlobalWf.drop_lookup n wf e zdef' zdef
      subst z'; assumption
  case mtch j1 j2 j3 j4 j5 j6 j7 j8 ih1 ih2 ih3 ih4 =>
    apply mtch
    apply ih1 wf e
    apply ValidTyHeadVariable.drop_weaken_global_is_data n wf e j2
    apply ih2 wf e
    intro i; apply ValidHeadVariable.drop_weaken_global_is_ctor n wf e (j4 i)
    intro i; apply ih3 i wf e
    apply j6
    intro i; apply ih4 i wf e
    apply j8
  case guard j1 j2 j3 j4 j5 j6 j7 ih1 ih2 ih3 =>
    apply guard
    apply ih1 wf e
    apply ih2 wf e
    apply ih3 wf e
    apply ValidHeadVariable.drop_weaken_global_is_instty n wf e j4
    apply ValidTyHeadVariable.drop_weaken_global_is_opent n wf e j5
    apply j6
    apply j7
  case lam j1 j2 ih =>
    apply lam
    apply Kinding.drop_weaken_global n wf e j1
    apply ih wf e
  case app j1 j2 j3 ih1 ih2 =>
    apply app
    apply Kinding.drop_weaken_global n wf e j1
    apply ih1 wf e
    apply ih2 wf e
  case lamt j1 j2 ih =>
    apply lamt
    apply Kinding.drop_weaken_global n wf e j1
    apply ih wf e
  case appt j1 j2 j3 ih =>
    apply appt
    apply ih wf e
    apply Kinding.drop_weaken_global n wf e j2
    apply j3
  case cast j1 j2 ih1 ih2 =>
    apply cast
    apply ih1 wf e
    apply ih2 wf e
  case refl j =>
    apply refl
    apply Kinding.drop_weaken_global n wf e j
  case sym j ih =>
    apply sym
    apply ih wf e
  case seq j1 j2 ih1 ih2 =>
    apply seq
    apply ih1 wf e
    apply ih2 wf e
  case appc j1 j2 ih1 ih2 =>
    apply appc
    apply ih1 wf e
    apply ih2 wf e
  case arrowc j1 j2 ih1 ih2 =>
    apply arrowc
    apply ih1 wf e
    apply ih2 wf e
  case fst j1 j2 j3 ih =>
    apply fst
    apply Kinding.drop_weaken_global n wf e j1
    apply Kinding.drop_weaken_global n wf e j2
    apply ih wf e
  case snd j1 j2 j3 ih =>
    apply snd
    apply Kinding.drop_weaken_global n wf e j1
    apply Kinding.drop_weaken_global n wf e j2
    apply ih wf e
  case allc j ih =>
    apply allc
    apply ih wf e
  case apptc j1 j2 j3 j4 ih1 ih2 =>
    apply apptc
    apply ih1 wf e
    apply ih2 wf e
    apply j3
    apply j4
  case zero j =>
    apply zero
    apply Kinding.drop_weaken_global n wf e j
  case choice j1 j2 j3 ih1 ih2 =>
    apply choice
    apply Kinding.drop_weaken_global n wf e j1
    apply ih1 wf e
    apply ih2 wf e

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
  case ctor j1 j2 j3 j4 j5 =>
    apply EntryWf.ctor
    apply GlobalWf.lookup_weaken wf j1
    apply j2
    apply Kinding.drop_weaken_global 1 wf (by simp) j3
    apply j4
    apply GlobalWf.lookup_weaken wf j5
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

theorem EntryWf.from_lookup_vec1 :
  Vect.fold d Option.or v = some t ->
  (∃ i, v i = some t) ∨ d = some t
:= by
  intro h
  induction v using Vect.induction
  case nil => simp at *; exact h
  case cons hd tl ih =>
    simp at h; rcases h with h | ⟨h1, h2⟩
    subst h; apply Or.inl; exists 0
    subst h1; replace ih := ih h2
    cases ih
    case _ ih =>
      obtain ⟨i, ih⟩ := ih
      apply Or.inl; exists (Fin.succ i)
    case _ ih => apply Or.inr ih

theorem EntryWf.from_lookup_vec2 :
  (∃ i, v i = some t ∧ (∀ j ≠ i, v j = none)) ->
  Vect.fold none Option.or v = some t
:= by
  intro h
  obtain ⟨i, h1, h2⟩ := h
  induction v using Vect.induction
  case nil =>
    exfalso; apply Fin.elim0 i
  case cons hd tl ih =>
    cases i using Fin.cases <;> simp at *
    case zero => apply Or.inl h1
    case succ i =>
      have h3 := λ j => h2 (Fin.succ j); simp at h3
      replace ih := ih i h1 h3
      apply Or.inr; apply And.intro _ ih
      apply h2 0; intro h; cases h

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
    case data dx K ctors j1 j2 j3 =>
      split at h
      case _ e1 =>
        subst e1; injection h with e; subst e
        apply EntryWf.data; simp [lookup]
      case _ e1 =>
        replace h := from_lookup_vec1 h
        rcases h with ⟨i, h⟩ | h
        case _ =>
          simp at h; obtain ⟨h1, h2⟩ := h
          rw [<-h2]
          generalize zdef : ctors i = z at *
          rcases z with ⟨z, zA⟩
          simp at *; subst h1
          obtain ⟨q1, q2, q3, q4⟩ := j2 i x zA zdef
          apply EntryWf.ctor dx K ctors; simp [lookup]
          exact zdef; exact q1
          exact q2; simp [lookup]
          split; case _ e => exfalso; apply e1 e
          case _ e =>
            rw [q4]
            apply from_lookup_vec2
            exists i; rw [zdef]; simp
            intro j w1 w2; apply j1 i j
            rw [<-w2, zdef]
        case _ => apply weaken wf' (ih h)
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
    case inst y T t j1 j2 =>
      replace ih := ih h
      apply weaken wf' ih
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
  ∃ b, G&Δ ⊢ T : .base b
:= by
  intro wf e; cases e; case _ b j1 j2 =>
  apply And.intro
  apply Typing.global; simp [lookup_type]; rw [j2]; simp
  simp [Entry.type]
  apply Kinding.closed_arbitrary_weakening Δ wf j1
  exists b; apply Kinding.closed_arbitrary_weakening Δ wf j1

theorem GlobalWf.types_have_base_kind :
  ⊢ G ->
  lookup_type G x = some T ->
  ∃ b, G&Δ ⊢ T : .base b
:= by
  intro wf h
  simp [lookup_type] at h
  generalize zdef : lookup x G = z at h
  cases z; simp at h; case _ z =>
  have lem := EntryWf.from_lookup wf zdef
  cases lem <;> simp [Entry.type] at h
  case ctor j1 j2 j3 j4 j5 =>
    apply Exists.intro _; subst h
    apply Kinding.closed_arbitrary_weakening Δ wf j4
  case openm j1 j2 =>
    apply Exists.intro _; subst h
    apply Kinding.closed_arbitrary_weakening Δ wf j1
  case defn j1 j2 j3 =>
    apply Exists.intro _; subst h
    apply Kinding.closed_arbitrary_weakening Δ wf j1
  case instty j1 j2 =>
    obtain ⟨b, lem⟩ := ValidInstTy.closed j1
    subst h; exists b
    apply Kinding.closed_arbitrary_weakening Δ wf lem

theorem GlobalWf.lookup_type_sound :
  ⊢ G ->
  lookup_type G x = some T ->
  G&Δ,Γ ⊢ g#x : T := by
 intro wf h
 have lem := GlobalWf.types_have_base_kind (Δ := Δ) wf h;
 rcases lem with ⟨bk, lem⟩
 constructor; assumption;
 apply lem;

theorem GlobalWf.lookup_defn_type_exists {G : List Global} {Δ : List Kind} :
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
  ∃ T b, G&Δ, Γ ⊢ g#x : T ∧ G&Δ, Γ ⊢ t : T ∧ G&Δ ⊢ T : .base b
:= by
  intro wf j
  unfold lookup_defn at j; simp at j
  obtain ⟨a, j1, j2⟩ := Option.bind_eq_some_iff.1 j; clear j
  have lem := EntryWf.from_lookup wf j1
  cases lem <;> simp at j2
  case _ T b t y q1 q2 q3 =>
  subst j2; exists T; exists b; apply And.intro
  apply Typing.global; simp [lookup_type]; rw [j1]; simp [Entry.type]
  apply Kinding.closed_arbitrary_weakening Δ wf q1
  apply And.intro
  replace q2 := Typing.weaken_type_closed Δ wf q2
  apply Typing.weaken_closed Γ wf q2
  apply Kinding.closed_arbitrary_weakening Δ wf q1

end Core
