import LeanSubst
import Core.Vec
import Lilac.Vect
import Surface.Ty
import Surface.Term

open LeanSubst

namespace Surface

inductive Global : Type where
| data : {n : Nat} -> String -> Kind -> Vect n (String × Ty) -> Global
| defn : String -> Ty -> Term -> Global
| classDecl : {n : Nat} -> String -> Kind -> /- Fundeps -> Vect k (Nat × Nat) -/  Vect n (String × Ty) -> Global
| instDecl : {n : Nat} -> Ty -> Vect n (String × Term) -> Global


def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data s K ctors =>
  (Std.Format.text ".data ") ++ (Std.Format.text s) ++ " : "
    ++ (Kind.repr max_prec K) ++ (Std.Format.text "where") ++
    Std.Format.line ++ Std.Format.nest 4 (ctors.reprPrec 0)
| .defn n T t => ".defn " ++ n ++ " " ++ T.repr max_prec ++ t.repr max_prec
| classDecl s K methods =>
  ".class " ++ s ++ " : " ++ Kind.repr max_prec K
    ++ Std.Format.line ++ (methods.reprPrec 0)
| instDecl t methods =>
  (Std.Format.text ".class ") ++ (Ty.repr max_prec t) ++ " : "
    ++ Std.Format.line ++ Std.Format.nest 4 (methods.reprPrec 0)

@[simp]
instance instRepr_Global : Repr Global where
  reprPrec a p := Global.repr p a

@[simp]
def GlobalEnv := List Global

@[simp] instance instHAppend_Globals : Append GlobalEnv where
  append x y := by unfold GlobalEnv; unfold GlobalEnv at x; unfold GlobalEnv at y; apply x ++ y

def Globals.repr (p : Nat) : GlobalEnv -> Std.Format
| .nil => Std.Format.nil
| .cons g gl => Global.repr 0 g ++ Globals.repr p gl

@[simp]
instance instRepr_Globals : Repr GlobalEnv where
  reprPrec a p := Globals.repr p a

inductive Entry : Type where
| data : String -> Kind -> Vect n (String × Ty) -> Entry
| ctor : String -> Nat -> Ty -> Entry
| defn : String -> Ty -> Term -> Entry
| opent : String -> Kind -> Vect n (String × Ty) -> Entry
| openm : String -> Nat -> Ty -> Entry

def Entry.is_data : Entry -> Bool
| data _ _ _ => true
| _ => false

def Entry.is_ctor : Entry -> Bool
| ctor _ _ _ => true
| _ => false

def Entry.is_opent : Entry -> Bool
| opent _ _ _ => true
| _ => false

def Entry.is_openm : Entry -> Bool
| openm _ _ _ => true
| _ => false

def Entry.is_defn : Entry -> Bool
| defn _ _ _ => true
| _ => false

def Entry.kind : Entry -> Option Kind
| data _ K _ => K
| opent _ K _ => K
| _ => none

def Entry.type : Entry -> Option Ty
| ctor _ _ T => T
| openm _ _ T => T
| defn _ T _ => T
| _ => none


def lookup (x : String) : GlobalEnv -> Option Entry
| [] => none
| .cons (.data (n := n) y K ctors) tl =>
  let ctors' : Vect n (Option Entry) := λ i =>
    let (z, A) := ctors i
    if x == z then return .ctor z i A else none
  if x == y then return .data y K ctors
  else Vect.fold (lookup x tl) Option.or ctors'
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.classDecl (n := n) y K ms) tl =>
  let ms' : Vect n (Option Entry) := λ i =>
    let (z, A) := ms i
    if x == z then return .openm z i A else none
  if x == y then return .opent y K ms
  else Vect.fold (lookup x tl) Option.or ms'
| .cons (.instDecl _ _) tl => lookup x tl

def lookup_kind G x := lookup x G |> Option.map Entry.kind |> Option.get!
def lookup_type G x := lookup x G |> Option.map Entry.type |> Option.get!

def is_ctor G x := lookup x G |> Option.map Entry.is_ctor |> Option.get!
def is_data G x := lookup x G |> Option.map Entry.is_data |> Option.get!
def is_opent G x := lookup x G |> Option.map Entry.is_opent |> Option.get!
def is_openm G x := lookup x G |> Option.map Entry.is_openm |> Option.get!
def is_defn G x := lookup x G |> Option.map Entry.is_defn |> Option.get!

def ctor_idx (x : String) (G : GlobalEnv) : Option Nat := do
  let t <- lookup x G
  match t with
  | .ctor _ n _ => n
  | _ => none

def ctor_ty (x : String) (G : GlobalEnv) : Option Ty := do
  let t <- lookup_type G x
  if is_ctor G x then return t else none

def ctor_count (x : String) (G : GlobalEnv) : Option Nat := do
  let t <- lookup x G
  match t with
  | .data _ _ ctors => ctors.length
  | _ => .none

def is_stable (x : String) (G : GlobalEnv) : Bool := is_ctor G x

def Ty.valid_data_type (G : GlobalEnv) (A : Ty) : Option Unit := do
  let (x, _) <- A.spine
  if is_data G x
  then return () else none

def Ty.valid_ctor_type (G : GlobalEnv) : (A : Ty) -> Option String
| .all _ T => T.valid_ctor_type G
| .arrow _ B => B.valid_ctor_type G
| t => do
  let (x, _) <- t.spine
  if is_data G x then return x else none




theorem lookup_entry_openm_exists :
  is_openm G x -> ∃ k T, lookup x G = .some (Entry.openm x k T) := by
intro h
generalize edef : lookup x G = e at *
fun_induction lookup <;> simp [is_openm] at *
case _ => simp [lookup] at h
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ ih => simp [lookup] at h; apply ih h edef



-- theorem lookup_entry_defn_exists :
--   is_defn G x -> ∃ y T t, lookup x G = .some (Entry.defn y T t) := by
-- intro h
-- simp [is_defn] at h
-- generalize edef : lookup x G = e at *
-- cases e <;> simp at h
-- case _ e =>
-- cases e <;> simp [Entry.is_defn] at h
-- case _ y T t => exists y; exists T; exists t

-- theorem lookup_defn_is_defn_sound :
--   lookup_defn G x = .some t -> is_defn G x := by
-- intro h; rw[is_defn]; rw[lookup_defn] at h; simp [Option.bind] at h
-- generalize zdef : lookup x G = z at *
-- cases z <;> simp at *
-- case _ z =>
-- cases z <;> simp [Entry.is_defn] at *


-- theorem lookup_defn_some :
--   lookup_defn G x = .some t -> ∃ y T t, lookup x G = .some (Entry.defn y T t) := by
-- intro h1
-- replace h1 := lookup_defn_is_defn_sound h1
-- apply lookup_entry_defn_exists h1

-- theorem is_stable_implies_not_is_openm :
--   is_stable G x -> ¬ is_openm x G := by
-- intro h1 h2
-- simp [is_stable] at h1;
-- cases h1
-- all_goals (
--   case _ h1 =>
--     have lem := lookup_entry_openm_exists h2
--     rcases lem with ⟨_, _, lem⟩
--     simp [is_ctor, is_instty] at h1; rw[lem] at h1
--     simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
-- )


-- theorem is_stable_implies_not_is_defn :
--   is_stable G x -> ¬ is_defn x G := by
-- intro h1 h2
-- simp [is_stable] at h1;
-- cases h1
-- all_goals (
--   case _ h1 =>
--     have lem := lookup_entry_defn_exists h2
--     rcases lem with ⟨_, _, _, lem⟩
--     simp [is_ctor, is_instty] at h1; rw[lem] at h1
--     simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
-- )

theorem Global.lookup_unique :
  lookup x G = some t ->
  lookup x G = some t' ->
  t = t' := by
intro h1 h2
all_goals (rw[h1] at h2; injection h2)

theorem Global.lookup_type_unique :
  lookup_type x G = some t ->
  lookup_type x G = some t' ->
  t = t' := by
intro h1 h2
all_goals (rw[h1] at h2; injection h2)

theorem Global.lookup_kind_unique :
  lookup_kind x G = some t ->
  lookup_kind x G = some t' ->
  t = t' := by
intro h1 h2
all_goals (rw[h1] at h2; injection h2)

end Surface
