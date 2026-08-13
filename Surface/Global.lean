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
| classDecl : {kc : Nat} ->
  String -> Vec Kind kc -> -- TODO Change Vec to List for SC and determiners of FDs and methods
  List (String × String × List (Fin kc)) ->
  List (String × (n : Nat) × Vec (Fin kc) (n + 1) × Fin kc) ->
  List (String × SpineTy) -> Global
| instDecl : String -> SpineTy -> List (String × Term) -> Global  -- what to do with instance constraints and ty params?


def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data s K ctors =>
  (Std.Format.text ".data ") ++ (Std.Format.text s) ++ " : "
    ++ (Kind.repr max_prec K) ++ (Std.Format.text " where ") ++
    Std.Format.line ++ Std.Format.nest 4 (ctors.reprPrec 0)
| .defn n T t => ".defn " ++ n ++ " " ++ (T.repr max_prec) ++ t.repr max_prec
| classDecl s Ks scs fds methods =>
  ".class " ++ s ++ " : " ++ Ks.repr max_prec ++ "|"  ++ scs.repr max_prec
    ++ "|" ++ fds.repr max_prec ++ (Std.Format.text " where ")
    ++ Std.Format.line ++ (methods.repr max_prec)
| instDecl i_name spTy methods =>
  (Std.Format.text ".inst ") ++ i_name ++ " : " ++ "⟨" ++ spTy.repr max_prec ++ "⟩"
    ++ Std.Format.line ++ Std.Format.nest 4 (methods.repr max_prec)

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
| openm : String -> SpineTy -> Entry

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
| openm _ _ => true
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
| .cons (.classDecl (kc := kc) y Ks scs fds ms) tl =>
  let ms_mb : Option (String × SpineTy) := ms.find? (λ (mn, _) => x == mn)
  let ms := ms_mb.map (λ (x, mn) => .openm x mn)
  let scs_mb : Option (String × String × List (Fin kc)) := scs.find? (λ (sc, _, _) => x == sc)
  let scs := scs_mb.map (λ (scn, cls, tys) => .openm scn ⟨kc, Ks, 0, #(), 1, #((gt`#y).mkApps_nats (List.range kc)), (gt`#cls).mkApps_nats tys⟩ )
  -- let fds_mb : Option (String × (n : Nat) × Vec (Fin kc) (n + 1) × Fin kc) := fds.find? (λ ⟨fdn, _, _, _⟩ => x == fdn)
  -- let fds := fds_mb.map (λ ⟨fdn, n, dns, dt⟩ => Entry.openm fdn ⟨kc, Ks, 0, #(), 2, #(sorry, sorry), t`#0 ⟩)
  if x == y then return .odata y Ks
  else if ms.isSome then ms
  else if scs.isSome then scs
  -- else if fds.isSome then fds
  else lookup x tl
| .cons (.instDecl s spTy _) tl =>
  if x == s then return .octor s spTy
  else lookup x tl

def lookup_kind (G : GlobalEnv) (x : String) : Option Kind := lookup x G |> Option.map Entry.kind |> Option.get!


-- def is_ctor (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_ctor |> Option.get!
-- def is_data (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_data |> Option.get!
-- def is_opent (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_odata |> Option.get!
-- def is_openm (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_openm |> Option.get!
-- def is_defn (G : GlobalEnv) x := lookup x G |> Option.map Entry.is_defn |> Option.get!

-- def ctor_idx (x : String) (G : GlobalEnv) : Option Nat := do
--   let t <- lookup x G
--   match t with
--   | .ctor _ n _ => n
--   | _ => none

-- def Entry.name : Entry -> String
-- | .data n _ _
-- | .ctor n _ _
-- | .defn n _ _
-- | .odata n _
-- | .octor n _
-- | .openm n _ => n

end Surface
