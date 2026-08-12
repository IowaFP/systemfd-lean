
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

inductive Entry : Type where
| data : {n : Nat} -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Entry
| ctor : String -> Nat -> Core.SpineTy -> Entry
| odata : String -> Core.Kind -> Entry
| openm : String -> Core.SpineTy -> Entry
| defn : String -> Core.Ty -> Surface.Term -> Entry
| octor : String -> Core.SpineTy -> Entry

def lookup (x : String) : List Global -> Option Entry := sorry

inductive DataConst where
| opn
| cls

def Entry.ctor? (data : String) : DataConst -> Entry -> Bool
| .cls, ctor _ _ ⟨_, _, _, _, _, _, T⟩ | .opn, octor _ ⟨_, _, _, _, _, _, T⟩ =>
  match T.spine with
  | some ⟨d, _⟩ => d == data
  | none => false
| _, _ => false

def lookup_ctor? (G : GlobalEnv) (c : DataConst) (ctor : String) (data : Core.Ty) : Bool :=
  match data.spine with
  | some (x, _) => lookup ctor G |> Option.map (Entry.ctor? x c) |> Option.getD (dflt := false)
  | none => false


end Intermediate
