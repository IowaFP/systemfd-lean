import HM.Term
import Core.Ty

open LeanSubst


namespace HM

inductive Typing : List Ty -> Term -> Ty -> Prop where

@[simp]
abbrev TypeEnv := List Core.Ty

def algoW (Γ : TypeEnv) : Term -> Ty -> Subst Core.Ty
|

end HM
