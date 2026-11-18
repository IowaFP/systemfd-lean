import Core.Global
import Core.Term
import Core.Typing
import Core.Metatheory.Global
import Core.Reduction
import Core.Untyped

open Lilac
open LeanSubst
open List

namespace Core

@[simp]
def Pattern.erase (pm : Pattern m) : Untyped.Pattern m :=
  pm.map (fun ⟨s, _, _, i, j⟩ => (s, i, j))

/--
Erases both types and coercions.
-/
@[simp]
def Term.erase : Term → Untyped.Term
  | #x => #x
  -- Just like a variable
  | d#x => d#x
  | spctor _ x _ _ ts => .spctor x (Term.erase <$> ts)
  | ctor0 (.refl _) => .unit
  | ctor1 (.appt _) b => .app b.erase .unit
  | ctor1 (.prj _) t => t.erase
  | ctor2 .app t1 t2 => .app t1.erase t2.erase
  | ctor2 .apptc _ _ => .unit
  | lam _ t => .lam t.erase
  | tbind .allc _ t => t.erase
  | tbind .lamt _ t => .lam t.erase
  | cast _ _ t => t.erase
  | mtch m n vm pmn vn => 
    .mtch m n (erase <$> vm) (Pattern.erase <$> pmn) (erase <$> vn)


-- TODO: define erase on Subst Term
-- beta rule for subs

@[simp]
def Constructor.erase (c : Constructor) : Untyped.Constructor :=
  let ⟨s, _, _, _, _, n, vm⟩ := c
  ⟨s, n, vm.map Term.erase⟩

@[simp]
def Global.erase : Global → Untyped.Global
| defn s _ t => .defn s t.erase
| inst s pm t => .inst s pm.erase t.erase
-- To simplify indexing,
-- use a dummy variant
| _ => .erased

@[simp]
def GlobalEnv.erase (G : GlobalEnv) := Global.erase <$> G

notation "⟦" e "⟧" => Term.erase e
notation "⟦" g "⟧" => Global.erase g
notation "⟦" G "⟧" => GlobalEnv.erase G
notation "⟦" pm "⟧" => Pattern.erase pm
notation "⟦" vm "⟧" => Term.erase <$> vm
notation "⟦" pmn "⟧" => Pattern.erase <$> pmn

theorem Pattern.erasure_subst (σ : Subst Ty) : (m : Nat) → (pmn : Pattern m) →
  ⟦pmn.smap σ⟧ = pmn.erase
| 0, .nil => by rfl
| n + 1, .cons _ _ => by 
  simp; apply Pattern.erasure_subst

theorem erasure_subst_ty (σ : Subst Ty) : (b : Term) → ⟦b[σ]⟧ = ⟦b⟧
| #x | d#x | .ctor0 _ => by rfl
| .spctor v s v1 v2 ts => by
  simp [Term.erase]; funext;
  apply ((fun b' => erasure_subst_ty σ b') <$> ts)
| .ctor1 (.appt _) b => by simp; apply erasure_subst_ty σ b
| .ctor1 (.prj n) b => by simp; apply erasure_subst_ty σ b
| .ctor2 .app t1 t2 => by
    simp
    apply And.intro
    apply erasure_subst_ty
    apply erasure_subst_ty
| .ctor2 .apptc _ _ => by rfl
| .cast _ _ t => by simp; apply erasure_subst_ty
| .tbind .allc _ t => by simp; apply erasure_subst_ty
| .tbind .lamt _ t => by simp; apply erasure_subst_ty
| .mtch m n vm pmn vn => by
    simp; apply And.intro; funext;
    apply ((fun b' => erasure_subst_ty σ b') <$> vm)
    apply And.intro; funext;
    apply Pattern.erasure_subst
    funext;
    apply erasure_subst_ty
| .lam _ t => by simp; apply erasure_subst_ty

theorem erasure_subst_ty_su (b : Term)(t : Ty):
  ⟦b[su t::+0σ]⟧ = ⟦b⟧ := by apply erasure_subst_ty

theorem Untyped.lookup_append_weaken_right :
  Untyped.lookup x G1 = some e → Untyped.lookup x (G1++G2) = some e := by
  intro h
  induction G1
  simp[Untyped.lookup] at h
  case _ head tail ih =>
    cases head; simp
    · simp [Untyped.lookup] at h; split at h <;> try simp at h
      case _ e => subst x; simp; apply h
      case _ e =>
        simp [e];
        apply ih h
    case _ m s pm t => 
      simp [Untyped.lookup]
      simp [Untyped.lookup] at h
      exact ih h
    case _=> 
      simp [Untyped.lookup]
      simp [Untyped.lookup] at h
      exact ih h

theorem GlobalEnv.lookup_singleton_defn_some :
  lookup x [Global.defn x a t] = some (.defn x a t) := by simp[lookup]

theorem GlobalEnv.lookup_singleton_some_eq :
  lookup x1 [Global.defn y a1 t1] = some (.defn x2 a2 t2)
  → x1 = y ∧ x1 = x2 ∧ a1 = a2 ∧ t1 = t2 := by
  unfold lookup
  intros h
  split at h
  grind
  contradiction

theorem GlobalEnv.lookup_inst_none :
  lookup x [.inst s pm t] = none := by simp[lookup]

theorem GlobalEnv.lookup_data:
  lookup x [.data n y K ctors] = some (.data y K ctors) := by 
  simp[lookup]
  intros
  sorry

theorem GlobalEnv.lookup_odata:
  lookup x [.odata n y] = some (.odata n y) := by 
  simp[lookup]
  sorry

theorem GlobalEnv.lookup_singleton_elim :
  lookup x [g] = some (.defn y a t)
  → x = y
  := by
  intros h
  cases g
  case _ n y K ctors => 
    have h2 := @GlobalEnv.lookup_data x n y K ctors
    rw[h2] at h
    grind
  case _ => 
    unfold lookup at h
    sorry
  -- case _ _ n y K ctors _ heq => 
  --   injection heq with head_eq
  --
  --   sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

theorem GlobalEnv.lookup_from_some :
  lookup x [g] = some (.defn x a t)
  → g = .defn x a t := by 
  intros h
  unfold lookup at h
  split at h <;> try simp
  case h_1 => trivial
  case h_2 n y _ _ _ _ => 
    simp at h
    split at h
    injection h
    contradiction
    rename_i heq hxy
    injection heq with head_eq tail_eq
    unfold Vec.foldr at h
    split at h
    case _ => 
      rw[←tail_eq] at h
      contradiction
    case _ => sorry
  case h_3 heq => 
    split at h
    injection h; contradiction
    injection heq with head_eq tail_eq
    rw[←tail_eq] at h
    contradiction
  case h_4 heq =>
    injection heq with head_eq
    sorry
  case h_5 => sorry
  case h_6 => sorry
  case h_7 => sorry

theorem GlobalEnv.lookup_nomatch :
  lookup x [.defn y a t] = none → x ≠ y := by 
  intros h hxy
  subst hxy
  have h2 := @GlobalEnv.lookup_singleton_defn_some x a t
  rw[h2] at h
  contradiction

theorem Untyped.lookup_singleton_elim :
  Untyped.lookup x [g] = some (.defn y t)
  → x = y
  := by 
  intros h
  unfold Untyped.lookup at h
  split at h
  contradiction
  case _ => sorry
  case _ => sorry

theorem lookup_erasure_singleton_some :
 lookup x [g] = some (.defn y a t)
  → Untyped.lookup x [⟦g⟧] = some (.defn y ⟦t⟧)
  := by
    intros h
    simp
    split
    case h_1 => 
      simp
      let ⟨hx1y, hx12, ha12, ht12⟩ := GlobalEnv.lookup_singleton_some_eq h
      apply And.intro
      exact hx1y
      apply And.intro
      rw[←hx1y, hx12]
      rw[ht12]
    case h_2 =>
      simp
      rw[GlobalEnv.lookup_inst_none] at h
      contradiction
    case h_3 g' hp1 hp2 =>
      simp
      rw[GlobalEnv.lookup_singleton_elim h] at h
      have h2 := GlobalEnv.lookup_from_some h
      exact hp1 y a t h2

theorem lookup_erasure_singleton_none :
 lookup x [g] = none
  → Untyped.lookup x [⟦g⟧] = none
  := by
    intros h
    dsimp
    split
    simp[Untyped.lookup]
    case h_1 => exact GlobalEnv.lookup_nomatch h
    case h_2 => simp
    case h_3 => simp

theorem Untyped.lookup_elim_left (G : List Untyped.Global) :
  Untyped.lookup x G' = none
  → Untyped.lookup x (G'++G) = Untyped.lookup x G
  := by
    intros h
    sorry

theorem wf_weaken (wf : ⊢ (h :: ts)) : ⊢ ts := by 
  cases wf
  case cons wf _ => apply wf

theorem lookup_erasure (wf : ⊢ G) :
  lookup x G = some (Entry.defn y a t)
  → Untyped.lookup x (map Global.erase G)
    = some (Untyped.Entry.defn x ⟦t⟧) := by
  intro h1
  rcases G with _ | ⟨h, ts⟩
  contradiction
  rw[← List.singleton_append]
  rw[← List.singleton_append] at h1
  have h2 := (Core.lookup_append_some wf h1)
  rcases h2
  case _ heq => 
    rw [List.singleton_append, List.map_cons]
    have heq' := lookup_erasure_singleton_some heq
    rw[←(Untyped.lookup_singleton_elim heq')] at heq'
    apply Untyped.lookup_append_weaken_right heq'
  case _ h3 => 
    let ⟨h3l, h3r⟩ := h3; clear h3
    rw [List.singleton_append, List.map_cons]
    rw [←List.singleton_append]
    let G := map Global.erase ts
    rw[Untyped.lookup_elim_left G (lookup_erasure_singleton_none h3l)]
    rw[←lookup_erasure (wf_weaken wf) h3r]

-- TODO: avoid cases by matching on *G*,
-- JUST the List, not the globals
theorem GlobalEnv.erasure_ty (wf : ⊢ G) :
  lookup_defn G x = some (A, t)
  → Untyped.lookup_defn ⟦G⟧ x = ⟦t⟧ := by
  intro h
  simp[lookup_defn] at h
  simp[Option.bind_eq_some_iff] at h
  rcases h with ⟨e, h1, h2⟩
  cases e <;> (
    rename_i a t;
    try rename_i y;
    try simp at h2
  )
  rcases h2 with ⟨e1, e2⟩
  subst e1 e2
  simp[Untyped.lookup_defn, Functor.map, Option.bind_eq_some_iff]
  exists .defn x ⟦t⟧
  apply And.intro
  apply lookup_erasure wf h1
  rfl

-- theorem erasure_well_def (wf : ⊢ G)


-- theorem erasure_disjoint_index (wf : ⊢ G) (i j : Fin m): 
--   j ≠ i → ss j = ss' j
--   → ⟦ss j⟧ = ⟦ss' j⟧
--
-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily any steps at the top
-- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
-- TODO: determine why this broke!
| .beta => by sorry
    -- simp
    -- .step .beta
-- | betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| @Red.betat G t A b => by
  rw [erasure_subst_ty_su b t]
  simp
  sorry
  -- exact .step .beta
| .cast => .refl
| .prj_fst_app | .prj_snd_app => .refl
| .prj_fst_arr | .prj_snd_arr => .refl
-- FIXME: with previous rules, this reduces to λλ#0 → λ#0.
-- *Is* adding a reduction here safe,
-- OR should erase just for .allc?
| .allc | .apptc => .refl
| @Red.defn G x A t hdf => .step (.defn (GlobalEnv.erasure_ty wf hdf))
| .ctor1_congr (v := .appt _) (t := t) (t' := t') s
| .app_congr (f := t) (f' := t') s => by
  simp
  generalize h1 : ⟦t⟧ = et
  generalize h2 : ⟦t'⟧ = et'
  have ih := erasure wf s
  rw[h1, h2] at ih
  rcases ih with _ | hr
  exact .refl
  exact .step (.app_congr hr)
| .ctor1_congr (v := .prj _) s => by apply erasure wf s
| .apptc_congr1 _ | .apptc_congr2 _ | .cast_congr _ => .refl
| .allc_congr s => by apply erasure wf s
-- | data_match {ss : Fun.Vec Term m} {ps : Fun.Vec (Pattern m) n} :
--   Term.IsData .cls ss.to ctors ->
--   Pattern.Match ctors (ps i) ->
--   b' = (bs i)[Constructor.subst_type ctors ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
--   Red G (.mtch m n ss ps bs) b'
-- | openm_match {i : Nat} {ss : Fun.Vec Term m} :
--   Term.IsData .opn ss.to ctors ->
--   G[i]? = some (.inst x p b) ->
--   Pattern.Match ctors p ->
--   b' = b[Constructor.subst_type ctors ++ Ts2.list.reverse.map su ++ Ts1.list.reverse.map su ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
--   Red G (openm! x Ts1 Ts2 ss) b'
-- | openm_congr {ts : Fun.Vec Term n} i :
--   Red G (ts i) (ts' i) ->
--   (∀ j ≠ i, ts j = ts' j) ->
--   Red G (openm! x Ts1 Ts2 ts) (openm! x Ts1 Ts2 ts')
-- | match_congr {ss : Fun.Vec Term m} i :
--   Red G (ss i) (ss' i) ->
--   (∀ j ≠ i, ss j = ss' j) ->
--   Red G (.mtch m n ss ps bs) (.mtch m n ss' ps bs)
| @Red.match_congr G m ss' n ps bs ss i st a => by
    simp
    generalize hss' : ⟦ss' i⟧ = x'
    generalize hss : ⟦ss i⟧ = x
    let e := erasure wf st
    rw[hss', hss] at e
    cases e
    case _ =>
      have hfs : (fun n => ⟦ss n⟧) =  (fun n => ⟦ss' n⟧) := by grind
      rw[hfs]
      .exact .refl
    case _ st =>
      rw[←hss', ←hss] at st
      exact .step (@Untyped.Red.match_congr ⟦G⟧ m ⟦ss'⟧ n ⟦ps⟧ ⟦bs⟧ ⟦ss⟧ i st sorry)
| _ => sorry

