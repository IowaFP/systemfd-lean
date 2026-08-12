import LeanSubst
import Core.Vec
import Lilac
import Surface.Ty
import Surface.Term

open LeanSubst
open Lilac

namespace Surface

inductive Global where
| data : {n : Nat} -> String -> Kind -> Vec (String × SpineTy) n -> Global
| defn : String -> Ty -> Term -> Global
| classDecl : {mc kc fc sc : Nat} ->
  String -> Vec Kind kc ->
  Vec (String × Ty) sc ->
  Vec (String × Fin kc × Fin kc) fc ->
  Vec (String × SpineTy) mc -> Global
| instDecl : {mc : Nat} -> String -> SpineTy -> Vec (String × Term) mc -> Global


def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data s K ctors =>
  (Std.Format.text ".data ") ++ (Std.Format.text s) ++ " : "
    ++ (Kind.repr max_prec K) ++ (Std.Format.text " where ") ++
    Std.Format.line ++ Std.Format.nest 4 (ctors.reprPrec 0)
| .defn n T t => ".defn " ++ n ++ " " ++ (T.repr max_prec) ++ t.repr max_prec
| classDecl s Ks scs fds methods =>
  ".class " ++ s ++ " : " ++ Ks.repr max_prec ++ "|"  ++ scs.repr max_prec
    ++ "|" ++ fds.repr max_prec ++ (Std.Format.text " where ")
    ++ Std.Format.line ++ (methods.reprPrec 0)
| instDecl i_name spTy methods =>
  (Std.Format.text ".inst ") ++ i_name ++ " : " ++ "⟨" ++ spTy.repr max_prec ++ "⟩"
    ++ Std.Format.line ++ Std.Format.nest 4 (methods.reprPrec max_prec)

@[simp]
instance instRepr_Global : Repr (Global) where
  reprPrec a p := Global.repr p a

@[simp]
abbrev GlobalEnv := List (Global)

inductive Entry : Type where
| data : {n : Nat} -> String -> Kind -> Vec (String × SpineTy) n -> Entry
| ctor : String -> Nat -> SpineTy -> Entry
| defn : String -> Ty -> Term -> Entry
| odata : {n : Nat} -> String -> Vec Kind n -> Entry
| octor : String -> SpineTy -> Entry
| openm : String -> Nat -> SpineTy -> Entry

def Entry.is_data : Entry -> Bool
| data _ _ _ => true
| _ => false

def Entry.is_ctor : Entry -> Bool
| ctor _ _ _ => true
| _ => false

def Entry.is_odata : Entry -> Bool
| odata _ _ => true
| _ => false

def Entry.is_openm : Entry -> Bool
| openm _ _ _ => true
| _ => false

def Entry.is_defn : Entry -> Bool
| defn _ _ _ => true
| _ => false

def Entry.kind : Entry -> Option Kind
| data _ K _ => K
| odata _ Ks => Kind.mk_kind Ks
| _ => none


def lookup (x : String) : GlobalEnv -> Option (Entry)
| [] => none
| .cons (.data (n := n) y K ctors) tl =>
  let ctors' : Fun.Vec (Option (Entry)) n := λ i =>
    let (z, A) := ctors.to i
    if x == z then return .ctor z i A else none
  if x == y then return .data y K ctors
  else ctors'.to.foldl (init := lookup x tl) Option.or
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.classDecl (mc := n) y Ks _ _ ms) tl =>
  let ms' : Fun.Vec (Option (Entry)) n := λ i =>
    let (z, A) := ms.to i
    if x == z then return .openm z i A else none
  if x == y then return .odata y Ks
  else ms'.to.foldl (init := lookup x tl) Option.or
| .cons (.instDecl s spTy _) tl =>
  if x == s then return .octor s spTy
  else lookup x tl

def lookup_kind (G : GlobalEnv) (x : String) : Option Kind := lookup x G |> Option.map Entry.kind |> Option.get!


def is_ctor (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_ctor |> Option.get!
def is_data (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_data |> Option.get!
def is_opent (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_odata |> Option.get!
def is_openm (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_openm |> Option.get!
def is_defn (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_defn |> Option.get!

def ctor_idx (x : String) (G : GlobalEnv) : Option Nat := do
  let t <- lookup x G
  match t with
  | .ctor _ n _ => n
  | _ => none

def Entry.name : Entry -> String
| .data n _ _
| .ctor n _ _
| .defn n _ _
| .odata n _
| .octor n _
| .openm n _ _ => n

end Surface
