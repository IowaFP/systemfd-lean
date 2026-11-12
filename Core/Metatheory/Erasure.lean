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
  | tbind _ _ t => .lam t.erase
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
| .tbind _ _ t => by simp; apply erasure_subst_ty
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

-- theorem Untyped.drop_lookup_unique n :
--   Untyped.lookup x (G.drop n) = some t ->
--   Untyped.lookup x G = some t := by sorry

-- TODO: remove if needed
theorem Untyped.lookup_singleton :
  Untyped.lookup x [g] = some e → ∃ t, g = .defn x t := by
  intro h
  unfold Untyped.lookup at h
  split at h <;> try trivial
  rename_i y t _ heq
  exists t
  injection heq with heq htl
  split at h;
  rename_i eqxy
  rw[eq_of_beq eqxy]; trivial
  rw[←htl] at h
  simp at h
  rename_i heq x tl head
  injection head with hi ti
  rw[←ti] at h
  simp at h

theorem Untyped.lookup_weaken_tail : 
  Untyped.lookup x [g] = some e 
  -> Untyped.lookup x (g::G) = some e := by
  intro h
  unfold Untyped.lookup; simp
  split
  contradiction
  rename_i heq
  injection heq with head_eq tail_eq
  split


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
  sorry

theorem Untyped.lookup_weaken : Untyped.lookup x G = some e -> Untyped.lookup x (g::G) = some e := by
  intro h
  sorry

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
| .allc => by sorry
| @Red.apptc G K A B => .refl
| @Red.defn G x A t hdf => .step (.defn (GlobalEnv.erasure_ty wf hdf))
| .ctor1_congr (v := .appt _) s => sorry
| .ctor1_congr (v := .prj _) s => sorry
| _ => sorry
