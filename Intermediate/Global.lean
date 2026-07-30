
import Surface.Global
import Core.Global


import Lilac
open Lilac

namespace Intermediate

/-- Staged Global that contains pre-elaaborated terms, but compiled types and kinds -/
inductive Global : Type where
| data : (n : Nat) -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Global
| defn : String -> Core.Ty -> Surface.Term -> Global
-- | classDecl : {mc kc fc : Nat} -> String -> Vec Kind kc -> Vec (String × Fin kc × Fin kc) fc ->  Vec (String × Ty) mc -> Global
| odata : String -> Core.Kind -> Global
| openm : String -> Core.SpineTy -> Global
-- | instDecl : {kc mc : Nat} -> String -> String -> Vec Ty kc -> Vec (String × Term) mc -> Global
| octor  : String -> Core.SpineTy -> Global
| inst : {m : Nat} -> String -> Core.Pattern m -> Surface.Term -> Global


@[simp]
abbrev GlobalEnv := List Global


end Intermediate
