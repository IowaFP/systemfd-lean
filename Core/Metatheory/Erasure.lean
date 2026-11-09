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
def Term.erase : Term → Untyped.Term
  | #x => #x
  -- Just like a variable
  | d#x => d#x
  | spctor _ _ _ _ _ => sorry
  | ctor0 (.refl _) => .lam (.var 0)
  | ctor1 (.appt _) t => t.erase
  | ctor1 _ t => t.erase
  | ctor2 .app t1 t2 => .app t1.erase t2.erase
  | ctor2 .apptc t1 t2 => .unit
  | tbind _ _ t => t.erase
  | lam _ t => .lam t.erase
  | cast _ t1 t2 => t2.erase
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

theorem erasure_tbind (b : Term)(t : Ty):
  ⟦b[su t::+0σ]⟧ = ⟦b⟧ :=
match b with
| #x | d#x | .ctor0 _ => by rfl
| .mtch _ _ _ _ _ => by sorry
| _ => sorry

-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily any steps at the top
-- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
| .beta => .step .beta
-- | betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| @Red.betat G t A b => by 
  rw [erasure_tbind b t]
  exact .refl
| .cast => .refl
| .prj_fst_app | .prj_snd_app => .refl
| .prj_fst_arr | .prj_snd_arr => .refl
| .allc => .refl
| .apptc => by sorry
| @Red.defn G x A t hdf => by 
    have h : Untyped.lookup_defn x ⟦G⟧ = some ⟦t⟧ := by sorry
    exact .step (.defn h)
| .ctor1_congr _ => by sorry
| _ => sorry
