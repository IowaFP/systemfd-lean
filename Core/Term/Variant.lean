import LeanSubst
import Core.Term.Definition

open LeanSubst

def Term.not_choice : Term -> Bool
| ctor2 .choice _ _ => false
| _ => true
