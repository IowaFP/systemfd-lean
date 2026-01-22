import LeanSubst
import Core.Vec
import Core.Ty
import Core.Term

open LeanSubst

inductive Global : Type where
| data : String -> Kind -> Vec (String × Ty) n -> Global
| opent : String -> Kind -> Global
| openm : String -> Ty -> Global
| defn : String -> Ty -> Term -> Global
| inst : String -> Term -> Global
| instty : String -> Ty -> Global

inductive Entry : Type where
| data : String -> Kind -> Vec (String × Ty) n -> Entry
| ctor : String -> Nat -> Ty -> Entry
| opent : String -> Kind -> Entry
| openm : String -> Ty -> Entry
| defn : String -> Ty -> Term -> Entry
| instty : String -> Ty -> Entry

def Entry.is_data : Entry -> Bool
| data _ _ _ => true
| _ => false

def Entry.is_ctor : Entry -> Bool
| ctor _ _ _ => true
| _ => false

def Entry.is_opent : Entry -> Bool
| opent _ _ => true
| _ => false

def Entry.is_openm : Entry -> Bool
| openm _ _ => true
| _ => false

def Entry.is_defn : Entry -> Bool
| defn _ _ _ => true
| _ => false

def Entry.is_instty : Entry -> Bool
| instty _ _ => true
| _ => false

def Entry.kind : Entry -> Option Kind
| data _ K _ => K
| opent _ K => K
| _ => none

def Entry.type : Entry -> Option Ty
| ctor _ _ T => T
| openm _ T => T
| defn _ T _ => T
| instty _ T => T
| _ => none

def lookup (x : String) : List Global -> Option Entry
| [] => none
| .cons (.data (n := n) y K ctors) tl =>
  let ctors' : Vec (Option Entry) n := λ i =>
    let (z, A) := ctors i
    if x == z then return .ctor z i A else none
  if x == y then return .data y K ctors
  else Vec.fold Option.or (lookup x tl) ctors'
| .cons (.opent y a) tl =>
  if x == y then return .opent y a else lookup x tl
| .cons (.openm y a) tl =>
  if x == y then return .openm y a else lookup x tl
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.inst _ _) tl => lookup x tl
| .cons (.instty y a) tl =>
  if x == y then return .instty y a else lookup x tl

def instances (x : String) : List Global -> List Term
| [] => []
| .cons (.inst y t) tl =>
  if x == y then t :: instances x tl else instances x tl
| .cons _ tl => instances x tl

def lookup_kind G x := lookup x G |> Option.map Entry.kind |> Option.get!
def lookup_type G x := lookup x G |> Option.map Entry.type |> Option.get!
def is_ctor G x := lookup x G |> Option.map Entry.is_ctor |> Option.get!
def is_data G x := lookup x G |> Option.map Entry.is_data |> Option.get!
def is_instty G x := lookup x G |> Option.map Entry.is_instty |> Option.get!
def is_opent G x := lookup x G |> Option.map Entry.is_opent |> Option.get!
def is_openm G x := lookup x G |> Option.map Entry.is_openm |> Option.get!
def is_defn G x := lookup x G |> Option.map Entry.is_defn |> Option.get!

def ctor_idx (x : String) (G : List Global) : Option Nat := do
  let t <- lookup x G
  match t with
  | .ctor _ n _ => n
  | _ => none

def ctor_ty (x : String) (G : List Global) : Option Ty := do
  let t <- lookup x G
  match t with
  | .ctor _ _ ty => return ty
  | _ => none

def ctor_count (x : String) (G : List Global) : Option Nat := do
  let t <- lookup x G
  match t with
  | .data _ _ ctors => ctors.length
  | _ => .none

def is_stable (x : String) (G : List Global) : Bool := !is_openm G x
