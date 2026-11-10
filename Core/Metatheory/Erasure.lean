import Core.Term
import Core.Global
import Core.Reduction
import Core.Typing
import Core.Untyped

open Lilac
open LeanSubst
open List

namespace Core

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
  | ctor0 (.refl _) => .lam (.var 0)
  | ctor1 _ t => t.erase
  | ctor2 .app t1 t2 => .app t1.erase t2.erase
  | ctor2 .apptc _ _ => .unit
  | tbind _ _ t => t.erase
  | lam _ t => .lam t.erase
  | cast _ _ t => t.erase
  | mtch m n vm pmn vn => 
    .mtch m n (erase <$> vm) (Pattern.erase <$> pmn) (erase <$> vn)

def Constructor.erase (c : Constructor) : Untyped.Constructor :=
  let ⟨s, _, _, _, _, n, vm⟩ := c
  ⟨s, n, vm.map Term.erase⟩

def Global.erase : Global → Untyped.Global
| defn s _ t => .defn s t.erase
| inst s pm t => .inst s pm.erase t.erase
-- To simplify indexing,
-- use a dummy variant
| _ => .erased

def GlobalEnv.erase (G : GlobalEnv) := Global.erase <$> G

notation "⟦" e "⟧" => Term.erase e
notation "⟦" g "⟧" => Global.erase g
notation "⟦" G "⟧" => GlobalEnv.erase G

-- Sticky cases where types in terms:
-- (lambda [x] m)[x -> T] OR have y. weakening at x -> T or extend it
-- M •[x] [x -> T]
-- spctors, casts: generalization of application
-- include weakening
theorem erasure_subst_ty (b : Term)(t : Ty):
  ⟦b[su t::+0σ]⟧ = ⟦b⟧ :=
match b with
| #x | d#x | .ctor0 _ => by rfl
| .spctor v s v1 v2 ts => by
  simp [Term.erase]; funext;
  apply ((fun b' => erasure_subst_ty b' t) <$> ts)
| .ctor1 _ t => by simp; apply erasure_subst_ty t
| .ctor2 .app t1 t2 => by
    simp
    apply And.intro
    apply erasure_subst_ty t1
    apply erasure_subst_ty t2
| .ctor2 .apptc _ _ => by rfl
| .cast _ _ t => by simp; apply erasure_subst_ty t
| .tbind _ _ t => by
  simp;
  sorry
| .mtch _ _ vm pmn vn => by
    simp; funext; 
    -- apply ((fun b' => erasure_tbind b' t) <$> vm)
    sorry
| .lam _ t => by simp; apply erasure_subst_ty t

-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily any steps at the top
-- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
| .beta => .step .beta
-- | betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| @Red.betat G t A b => by 
  rw [erasure_subst_ty b t]
  exact .refl
  -- exact .refl
| .cast => .refl
| .prj_fst_app | .prj_snd_app => .refl
| .prj_fst_arr | .prj_snd_arr => .refl
| .allc => by sorry
| .apptc => by sorry
| @Red.defn G x A t hdf => by 
    have h : Untyped.lookup_defn x ⟦G⟧ = some ⟦t⟧ := by sorry
    exact .step (.defn h)
| .ctor1_congr _ => by sorry
| _ => sorry
