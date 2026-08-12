
import Surface.Global
import Core.Global
import Core.Ty

import Lilac
open Lilac

namespace Intermediate

/-- Staged Global that contains Surface level terms, but compiled types and kinds -/
inductive Global : Type where
| data : (n : Nat) -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Global
| defn : String -> Core.Ty -> Surface.Term -> Global
-- | classDecl : {mc kc fc : Nat} -> String -> Vec Kind kc -> Vec (String × Fin kc × Fin kc) fc ->  Vec (String × Ty) mc -> Global
| odata : String -> Core.Kind -> Global
| openm : String -> Core.SpineTy -> Global
-- | instDecl : {kc mc : Nat} -> String -> String -> Vec Ty kc -> Vec (String × Term) mc -> Global
| octor  : String -> Core.SpineTy -> Global
| inst : {m : Nat} -> String -> Core.Pattern m -> Surface.Term -> Global


def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data _ s K ctors =>
  ".data " ++ s ++ " : " ++ Core.Kind.repr max_prec K  ++ " where " ++ Std.Format.line
     ++ Std.Format.nest 4 (ctors.reprPrec 0)
| .odata n K => ".odata " ++ n ++ " " ++ K.repr max_prec
| .openm n ty => ".openm " ++ n ++ " : " ++ Core.SpineTy.repr ty
| .defn n T t => ".defn " ++ n ++ " " ++ T.repr max_prec ++ Std.Format.line ++ t.repr max_prec
| .inst n p t => ".inst " ++ n ++ " " ++ p.repr ++ " => " ++ t.repr max_prec
| .octor n ty => ".octor " ++ n ++ " " ++ Core.SpineTy.repr ty

@[simp]
instance instRepr_Global : Repr Global where
  reprPrec a p := Global.repr p a

@[simp]
abbrev GlobalEnv := List Global

inductive Entry : Type where
| data : {n : Nat} -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Entry
| ctor : String -> Nat -> Core.SpineTy -> Entry
| odata : String -> Core.Kind -> Entry
| openm : String -> Core.SpineTy -> Entry
| defn : String -> Core.Ty -> Surface.Term -> Entry
| octor : String -> Core.SpineTy -> Entry

def lookup (x : String) : GlobalEnv -> Option Entry := sorry

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
