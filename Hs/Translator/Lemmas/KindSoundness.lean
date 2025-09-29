import Hs.HsTerm
import Hs.Monad
import SystemFD.Term
import SystemFD.Judgment
import Hs.HsJudgment

import Hs.Translator.Kinds

import Mathlib.Data.Prod.Basic

set_option maxHeartbeats 500000

theorem kind_shape_split_arrow_aux (k : Term) (acc : List Term):
  Term.IsKind k ->
  (∀ a ∈ acc, a.IsKind) ->
  Term.split_kind_arrow_aux acc k = .some (κs, ret_κ) ->
  ret_κ.IsKind ∧ ∀ k ∈ κs, k.IsKind := by
intro h1 h2 h3
induction acc, k using Term.split_kind_arrow_aux.induct generalizing κs ret_κ <;> simp at h3
case _ Γ f a ih =>
  cases h1; case _ h1a h2a =>
  have lem : ∀ (a : Term), a ∈ f :: Γ → a.IsKind := by
    intro x h
    simp at h; cases h
    case _ h => cases h; assumption
    case _ h => apply h2 x h
  have ih := @ih κs ret_κ h2a lem h3
  assumption
case _ =>
  cases h1
  cases h3.1; cases h3.2
  constructor; constructor
  assumption

theorem kind_shape_split_arrow {k : Term} :
  k.IsKind ->
  Term.split_kind_arrow k = some (κs, ret_κ) ->
  ret_κ.IsKind ∧ ∀ k ∈ κs, k.IsKind := by
 intros h1 h2; simp at h2
 rw[Option.bind_eq_some] at h2;
 cases h2; case _ w h2 =>
 cases h2; case _ h2 e =>
 cases e
 have lem := @kind_shape_split_arrow_aux w.fst w.snd k [] h1 (by intros; simp at *) h2
 cases lem; case _ lem =>
 constructor;
 assumption
 simp; assumption

theorem kinding_split_arrow_aux {Γ :  Ctx Term} (k : Term) (acc : List Term) :
  ⊢ Γ ->
  Γ ⊢ k : □ ->
  (∀ a ∈ acc, Γ ⊢ a : □) ->
  Term.split_kind_arrow_aux acc k = .some (κs, ret_κ) ->
  Γ ⊢ ret_κ : □ ∧ ∀ k ∈ κs, Γ ⊢ k : □ := by
intro wf j1 h1 h2
induction acc, k using Term.split_kind_arrow_aux.induct <;> simp at *
case _ ih =>
  cases j1; case _ j1a j1b =>
  have ih' := ih j1b j1a h1 h2
  assumption
case _ =>
  cases h2.1; cases h2.2
  constructor
  constructor; assumption
  intro k k_in_κs;
  have h1' := @h1 k k_in_κs
  assumption

theorem kinding_split_arrow {Γ : Ctx Term} {k : Term} :
  ⊢ Γ ->
  Γ ⊢ k : □ ->
  Term.split_kind_arrow k = .some (κs, ret_κ) ->
  Γ ⊢ ret_κ : □ ∧ ∀ k ∈ κs.reverse, Γ ⊢ k : □ := by
intro wf j h
apply kinding_split_arrow_aux k [] wf j
simp
unfold Term.split_kind_arrow at h; simp at h
rw[Option.bind_eq_some] at h; cases h; case _ w h =>
cases h; case _ h e =>
cases e
simp; assumption


theorem kinding_mk_kind_arrow {Γ: Ctx Term} {ks : List Term} {ret_k : Term} :
  ⊢ Γ ->
  (∀ k ∈ ks, Γ ⊢ k : □) ->
  Γ ⊢ ret_k : □ ->
  Γ ⊢ ret_k.mk_kind_arrow ks : □ := by
  intro wf j1 j2
  induction ks using List.foldr.induct <;> simp at *
  assumption
  case _ ih =>  cases j1; constructor; assumption; apply ih; assumption

theorem compile_kind_size (k : HsTerm) :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  k.size = k'.size := by
intro wf  j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; simp
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  simp; rw[ih1, ih2]



theorem kind_split_mk_arrow_aux {Γ : List Term} {κs : List Term} {k : Term}:
  k.split_kind_arrow_aux Γ = .some (κs, ret_κ) ->
  ∃ κs', κs = κs' ++ Γ := by
 intro h
 induction Γ, k using Term.split_kind_arrow_aux.induct generalizing κs ret_κ <;> simp at h
 case _ f a ih =>
   have ih' := ih h
   cases ih'; case _ w e =>
   exists (w ++ [f])
   rw[e]; simp
 cases h.1; cases h.2; exists []

theorem kind_split_empty_κs {k ret_κ : Term} :
  Term.split_kind_arrow_aux [] k = some ([], ret_κ) ->
  k = ret_κ := by
intro h
induction [], k using Term.split_kind_arrow_aux.induct generalizing ret_κ <;> simp at h
case _ =>
 exfalso
 have lem := kind_split_mk_arrow_aux h
 cases lem; case _ lem => simp at lem
assumption

theorem kind_split_arrow_base {k : Term} :
  Term.split_kind_arrow_aux Γ k = .some (κs, ret_k) ->
  ret_k = ★ := by
intro h
induction Γ, k using Term.split_kind_arrow_aux.induct <;> simp at *
case _ ih => apply ih h
case _ => cases h; symm; assumption


theorem mk_arrow_kind_cons {k ret_k : Term} {ks : List Term}:
  (k -k> ret_k.mk_kind_arrow ks) = ret_k.mk_kind_arrow (k :: ks) := by simp


theorem kind_split_arrow_mk_arrow_law {k k' ret_k : Term} {ks : List Term} :
  (k -k> k').split_kind_arrow = .some (k :: ks, ret_k) ->
  ret_k.mk_kind_arrow (k :: ks) = (k -k> k') := by
  intro h;
  generalize p : k :: ks = ls at *
  induction ls using List.foldr.induct generalizing k ks <;> simp at *;
  case _ ih =>
    symm; rw[Option.bind_eq_some] at h;
    cases h; case _ w h =>
    cases h <;> simp at *
    case _ h1 e =>
    cases e.2
    rw[<-@Prod.mk.eta (List Term) Term w] at h1
    rw[e.1] at h1
    cases p;
    constructor;
    case _ e1 e2 =>
      subst e1; subst e2; simp at e;
      have lem := kind_split_arrow_base h1
      rw[lem]; rw[lem] at ih; rw[lem] at h1
      induction ks <;> simp at *
      sorry
      sorry
    symm; assumption

theorem kind_mk_arrow_split_arrow_law {ret_k k : Term} {ks : List Term}:
  ∀ k ∈ ks, k.IsKind ->
  ret_k.mk_kind_arrow ks = k ->
  k.split_kind_arrow = .some (ks, ret_k) := by
intro h1 h2
sorry


theorem compile_kind_shape_sound {k : HsTerm} :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Term.IsKind k' := by
intro wf j1 j2
induction c, k using compile_kind.induct generalizing k' <;> simp at *
cases j2; constructor
case _ k1 k2 ih1 ih2 =>
  cases j2; case _ j2 =>
  cases j2; case _ j2 =>
  cases j2; case _ h1 _ h2 =>
  cases j1; case _ h3 h4 =>
  cases h2; case _ h2 e =>
  cases e
  replace ih1 := ih1 h3 h1
  replace ih2 := ih2 h4 h2
  constructor; assumption; assumption


theorem compile_kind_sound {k : HsTerm} :
  ⊢ Γ ->
  HsTerm.IsKind k ->
  compile_kind Γ c k = .ok k' ->
  Γ ⊢ k' : c := by
intro wf e1 j;
induction c, k using compile_kind.induct generalizing k' <;> simp at *
case _ => cases j; constructor; assumption
case _ k1 k2 ih1 ih2 =>
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j; cases e1;
  case _ e1 e2 =>
  replace ih1 := ih1 e1 h1;
  replace ih2 := ih2 e2 h2;
  constructor; assumption; assumption


theorem compile_star_sort_inversion {Γ : Ctx Term} {k : HsTerm} {k' : Term}:
  compile_kind Γ c k = DsM.ok k' -> c = □ := by
intro h
induction c, k using compile_kind.induct <;> simp at *


theorem compile_star : compile_kind Γ □ `★ = DsM.ok ★ := by simp


theorem dsm_get_type_sound : ⊢ Γ ->
  DsM.toDsM s (Γ d@ h).get_type = .ok τ -> Γ ⊢ #h : τ := by
intro wf j
unfold DsM.toDsM at j
let gt := (Γ d@ h).get_type
generalize fh : Γ d@ h = f at *;
cases f;
all_goals try (
  simp at j;
  unfold Frame.get_type at j; simp at j
)
all_goals try (
  cases j; apply Judgment.var wf;
  unfold Frame.get_type; rw[fh]
)


theorem compile_kind_sound_2 {Γ : Ctx Term} {k : HsTerm} {c : Term}:
  ⊢ Γ ->
  k.IsKind ->
  c = □ ->
  ∃ k', compile_kind Γ c k = .ok k' ∧ Term.IsKind k' := by
intro wf h1 e
-- Ideally h1 and e come from the surface level typing judgment
induction h1 <;> simp at *
case _ =>
  exists ★;
  constructor;
  case _ =>
    unfold compile_kind;
    split <;> simp at *
    exfalso; contradiction

  case _ => constructor
case _ ih1 ih2 =>
  cases e
  cases ih1; case _ A' ih1 =>
  cases ih1
  cases ih2; case _ B' ih2 =>
  cases ih2
  exists (A' -k> B')
  constructor;
  simp; exists A'; constructor; assumption; exists B'; constructor; assumption; assumption

@[simp]
abbrev CompileKindSoundLemmaType (_ : HsCtx HsTerm) (Γ' : Ctx Term): (i : JIdx) -> JudgmentType i -> Prop
| .CtxJ => λ () => true
| .TypeJ => λ _ => true
| .TermJ => λ _ => true
| .KindJ => λ (k, c) => c = `□ -> ∃ (k' : Term), compile_kind Γ' □ k = .ok k' ∧ (Γ' ⊢ k' : □)

theorem compile_kind_sound_3 {Γ : HsCtx HsTerm} {Γ' : Ctx Term} :
  -- somthing about relating Γ and Γ' to make sure Γ' is wf?
  ⊢ Γ' ->
  HsJudgment i Γ jty ->
  -- k.IsKind ->
  CompileKindSoundLemmaType Γ Γ' i jty

  := by
intro wf j; induction j <;> simp at *
case _ =>
  constructor; assumption
case _ ih1 ih2 =>
  cases ih1; case _ k1 ih1 =>
  cases ih1;
  cases ih2; case _ k2 ih2 =>
  cases ih2;
  exists (k1 -k> k2)
  constructor
  exists k1;
  constructor;
  case _ => assumption
  case _ => exists k2
  constructor; assumption; assumption
