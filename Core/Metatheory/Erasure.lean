import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing
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
notation "⟦" pmn "⟧" => Pattern.erase pmn

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


theorem Untyped.lookup_head :
  Untyped.lookup x [.defn y t] = some e'
  → e' = .defn y t  := by sorry


-- theorem Untyped.drop_lookup_unique n :
--   Untyped.lookup x (G.drop n) = some t ->
--   Untyped.lookup x G = some t := by sorry

-- TODO: remove if needed
theorem Untyped.lookup_singleton :
  Untyped.lookup x [g] = some e → 
  Untyped.lookup x [g] = some (.defn x t) := by
  sorry
  -- unfold Untyped.lookup at h
  -- split at h <;> try trivial
  -- rename_i y t _ heq
--  rexists t
--   injection heq with heq htl
--   split at h;
--   rename_i eqxy
--   rw[eq_of_beq eqxy]; trivial
--   rw[←htl] at h
--   simp at h
--   rename_i heq x tl head
--   injection head with hi ti
--   rw[←ti] at h
--   simp at h
--
theorem Untyped.lookup_weaken_tail : 
  Untyped.lookup x [g] = some e 
  -> Untyped.lookup x (g::G) = some e := by
  intro h
  unfold Untyped.lookup; simp
  split
  contradiction
  rename_i y t tl heq
  injection heq with head_eq tail_eq
  -- let ⟨hge, eqxy⟩ := Untyped.lookup_singleton (y := y) (t := t) h

  sorry 
  sorry
  -- rcases G with _ | ⟨h1, t1⟩
  -- trivial
  -- unfold Untyped.lookup at h
  -- split at h
  -- contradiction
  -- {
  --   split at h
  --   unfold Untyped.lookup; simp
  --   rename_i y heq tl eql eqxy
  --   injection eql
  --   rename_i tail_eq head_eq
  --   -- apply Untyped.lookup_singleton h
  --   sorry
  --   sorry
  -- }

theorem Untyped.lookup_append_uniq (x : String) (t : Untyped.Term) (e :
    Untyped.Entry) :
  Untyped.lookup x [.defn x t] = some e
  → e = .defn x t := by sorry

theorem Untyped.lookup_id (x : String) (t : Untyped.Term):
  Untyped.lookup x [.defn x t] = some (.defn x t) := by simp

theorem Untyped.lookup_weaken_right :
  Untyped.lookup x G = some e → Untyped.lookup x (G'++G) = some e := by
  intro h
  rcases G with _ | ⟨hd, G', G⟩
  simp[Untyped.lookup] at h

  sorry
  -- unfold Untyped.lookup
  -- split
  -- case h_1 heq =>
  --   have hG : G = [] := (List.append_eq_nil_iff.mp heq).2
  --   rw[hG] at h
  --   contradiction
  -- sorry
  -- sorry

theorem GlobalEnv.lookup_cons_cases  (wf : ⊢ G) : 
  lookup x (h::ts) = some e
    → lookup x ([h]) = some e ∨ lookup x ts = some e := by sorry

theorem GlobalEnv.lookup_erasure (wf : ⊢ G) :
  lookup x G = some (Entry.defn y a t)
  → Untyped.lookup x (map Global.erase G)
    = some (Untyped.Entry.defn x ⟦t⟧) := by
  intro h1
  rcases G with _ | ⟨h, ts⟩
  contradiction
  have h2 := GlobalEnv.lookup_cons_cases wf h1
  cases h2
  sorry
  sorry

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
  apply GlobalEnv.lookup_erasure wf h1
  rfl

-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily any steps at the top
-- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
| .beta => .step .beta
-- | betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| @Red.betat G t A b => by
  rw [erasure_subst_ty_su b t]
  exact .step .beta
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
    sorry
    -- .step (.match_congr i a )
| _ => sorry
