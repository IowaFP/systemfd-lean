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

def Global.repr (p : Nat) : (a : Global) -> Std.Format
| .data (n := n + 1) s K ctors =>
  let ts : Vec Std.Format (n + 1) := λ i =>
    let (ctorN, ctorTy) := ctors i
    Std.Format.nest 4 <| ctorN ++ " : " ++ Ty.repr max_prec ctorTy

  ".data " ++ s ++ " : " ++ Kind.repr max_prec K ++ Std.Format.line
    ++ "v" ++ Std.Format.sbracket (Vec.fold (λ c acc => acc ++ ", " ++ Std.Format.line ++ c) Std.Format.nil ts)
| .data s K _ =>
  ".data " ++ s ++ " : " ++ Kind.repr max_prec K
| .opent n K => ".opent " ++ n ++ " " ++ K.repr max_prec
| .openm n T => ".openm " ++ n ++ " " ++ T.repr max_prec
| .defn n T t => ".defn " ++ n ++ " " ++ T.repr max_prec ++ t.repr max_prec
| .inst n t => ".inst " ++ n ++ " " ++  t.repr max_prec
| .instty n T => ".instTy" ++ n ++ " " ++  T.repr max_prec

@[simp]
instance instRepr_Global : Repr Global where
  reprPrec a p := Global.repr p a

@[simp]
def Globals := List Global

@[simp] instance instHAppend_Globals : Append Globals where
  append x y := by unfold Globals; unfold Globals at x; unfold Globals at y; apply x ++ y

def Globals.repr (p : Nat) : Globals -> Std.Format
| .nil => Std.Format.nil
| .cons g gl => Global.repr 0 g ++ Globals.repr p gl

@[simp]
instance instRepr_Globals : Repr Globals where
  reprPrec a p := Globals.repr p a

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

def lookup_defn G x := do
  let t <- lookup x G
  match t with
  | .defn _ _ t => return t
  | _ => none

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
  let t <- lookup_type G x
  if is_ctor G x then return t else none

def ctor_count (x : String) (G : List Global) : Option Nat := do
  let t <- lookup x G
  match t with
  | .data _ _ ctors => ctors.length
  | _ => .none

def is_stable (x : String) (G : List Global) : Bool := (is_ctor G x ∨ is_instty G x)

theorem lookup_entry_openm_exists :
  is_openm G x -> ∃ y T, lookup x G = .some (Entry.openm y T) := by
intro h
simp [is_openm] at h
generalize edef : lookup x G = e at *
cases e <;> simp at h
case _ e =>
cases e <;> simp [Entry.is_openm] at h
case _ x T => exists x; exists T

theorem lookup_entry_defn_exists :
  is_defn G x -> ∃ y T t, lookup x G = .some (Entry.defn y T t) := by
intro h
simp [is_defn] at h
generalize edef : lookup x G = e at *
cases e <;> simp at h
case _ e =>
cases e <;> simp [Entry.is_defn] at h
case _ y T t => exists y; exists T; exists t

theorem lookup_defn_is_defn_sound :
  lookup_defn G x = .some t -> is_defn G x := by
intro h; rw[is_defn]; rw[lookup_defn] at h; simp [Option.bind] at h
generalize zdef : lookup x G = z at *
cases z <;> simp at *
case _ z =>
cases z <;> simp [Entry.is_defn] at *



theorem is_stable_implies_not_is_openm :
  is_stable G x -> ¬ is_openm x G := by
intro h1 h2
simp [is_stable] at h1;
cases h1
all_goals (
  case _ h1 =>
    have lem := lookup_entry_openm_exists h2
    rcases lem with ⟨_, _, lem⟩
    simp [is_ctor, is_instty] at h1; rw[lem] at h1
    simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
)


theorem is_stable_implies_not_is_defn :
  is_stable G x -> ¬ is_defn x G := by
intro h1 h2
simp [is_stable] at h1;
cases h1
all_goals (
  case _ h1 =>
    have lem := lookup_entry_defn_exists h2
    rcases lem with ⟨_, _, _, lem⟩
    simp [is_ctor, is_instty] at h1; rw[lem] at h1
    simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
)

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
