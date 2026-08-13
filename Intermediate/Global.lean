
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


inductive DataConst where
| opn
| cls

def Entry.is_data : DataConst -> Entry -> Bool
| .cls, data _ _ _ => true
| .opn, odata _ _ => true
| _, _ => false

def Entry.kind : Entry -> Option Core.Kind
| data _ K _ => K
| odata _ K => K
| _ => none

def lookup (x : String) : GlobalEnv -> Option Entry
| [] => none
| .cons (.data _ y K ctors) tl =>
  let ctors' := Vec.map
    (λ ((z, A), i) => if x == z then some (Entry.ctor z i A) else none)
    (Vec.zipIdx ctors)
  if x == y then return .data y K ctors
  else Vec.foldl Option.or (lookup x tl) ctors'
| .cons (.odata y a) tl =>
  if x == y then return .odata y a else lookup x tl
| .cons (.openm y a) tl =>
  if x == y then return .openm y a else lookup x tl
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.inst _ _ _) tl => lookup x tl
| .cons (.octor y a) tl =>
  if x == y then return .octor y a else lookup x tl

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

def lookup_defn (G : List Global) (x : String) : Option (Core.Ty × Surface.Term) := do
  let t <- lookup x G
  match t with
  | .defn _ T t => return ⟨T, t⟩
  | _ => none

def lookup_kind G x := lookup x G |> Option.map Intermediate.Entry.kind |> Option.join
def is_data c G x := lookup x G |> Option.map (Entry.is_data c) |> Option.getD (dflt := false)

inductive SpCtorVariant : Type where
| openm
| data (c : DataConst)


end Intermediate
