
-- TODO: maybe describe the target language
-- as a separate type.

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
  | ctor1 (.prj n) t => sorry
  | ctor1 (.appt _) t => t.erase
  | ctor2 .app t1 t2 => .app t1.erase t2.erase
  | ctor2 .apptc t1 t2 => sorry
  | tbind _ _ t => t.erase
  | lam _ t => .lam t.erase
  | cast _ t1 t2 => t2.erase
  | mtch m n vm pmn vn => 
    .mtch m n (erase <$> vm) (Pattern.erase <$> pmn) (erase <$> vn)

deriving instance BEq for Global

def Global.erase : Global → Untyped.Global
| defn s _ t => .defn s t.erase
| inst s pm t => .inst s pm.erase t.erase
| _ => .defn "" .unit

def GlobalEnv_erase (G : GlobalEnv) : Untyped.GlobalEnv :=
  Global.erase <$> G

-- TODO: add erased contexts

notation "⟦" e "⟧" => Term.erase e
notation "⟦" G "⟧" => GlobalEnv_erase G

-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily many steps at the top
-- -- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
| @Red.beta G A b t => .step (@Untyped.Red.beta ⟦G⟧ ⟦b⟧ ⟦t⟧)
-- | betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| @Red.betat G t A b => by
    -- exact @Untyped.RedOpt.refl ⟦G⟧ ⟦(Λ[A] b) •[t]⟧
    sorry
| @Red.cast G R A t => 
    @Untyped.RedOpt.refl ⟦G⟧ ⟦Term.cast R (refl! A) t⟧
| _ => sorry
