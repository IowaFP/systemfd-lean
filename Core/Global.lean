import Core.Vec
import Core.Ty
import Core.Term

open Lilac
open LeanSubst

namespace Core

inductive Global : Type where
| data : (n : Nat) -> String -> Kind -> Vec (String × SpineTy) n -> Global
| odata : String -> Kind -> Global
| openm : String -> SpineTy -> Global
| defn : String -> Ty -> Term -> Global
| inst : String -> Pattern m -> Term -> Global
| octor : String -> SpineTy -> Global

def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data (n := n) s K ctors =>
  let cs : Fun.Vec Std.Format n := λ i =>
    let ctorN := (Vec.to ctors i).1
    let ctorTy := (Vec.to ctors i).2
    Std.Format.nest 4 <| ctorN ++ SpineTy.repr ctorTy
  ".data " ++ s ++ " : " ++ Kind.repr max_prec K ++ Std.Format.line
      ++ "#𝓋" ++ Std.Format.sbracket (cs.to.foldl (λ c acc => acc ++ ", " ++ Std.Format.line ++ c) Std.Format.nil)

| .odata n K => ".odata " ++ n ++ " " ++ K.repr max_prec
| .openm n ty => ".openm " ++ n ++ " : " ++ SpineTy.repr ty
| .defn n T t => ".defn " ++ n ++ " " ++ T.repr max_prec ++ t.repr max_prec
| .inst n _ t => "instance " ++ n ++ " " ++  t.repr max_prec
| .octor n ty => ".octor" ++ n ++ SpineTy.repr ty


@[simp]
instance instRepr_Global : Repr Global where
  reprPrec a p := Global.repr p a

@[simp]
abbrev GlobalEnv := List Global

@[simp] instance instHAppend_GlobalEnv : Append GlobalEnv where
  append x y := by unfold GlobalEnv; unfold GlobalEnv at x; unfold GlobalEnv at y; apply x ++ y

-- def GlobalEnv.repr (p : Nat) : GlobalEnv -> Std.Format
-- | .nil => Std.Format.nil
-- | .cons g gl => Global.repr 0 g ++ Std.Format.line ++ GlobalEnv.repr p gl

-- @[simp]
-- instance instRepr_GlobalEnv : Repr GlobalEnv where
--   reprPrec a p := GlobalEnv.repr p a

inductive Entry : Type where
| data : String -> Kind -> Vec (String × SpineTy) n -> Entry
| ctor : String -> Nat -> SpineTy -> Entry
| odata : String -> Kind -> Entry
| openm : String -> SpineTy -> Entry
| defn : String -> Ty -> Term -> Entry
| octor : String -> SpineTy -> Entry

-- def Entry.repr (_ : Nat) : Entry -> Std.Format
-- | .data (n := n) x K ctors =>
--   let cs : Fun.Vec Std.Format n := λ i =>
--     let ctorN := (Vec.to ctors i).1
--     let ctorTy := (Vec.to ctors i).2
--     Std.Format.nest 4 <| ctorN ++ SpineTy.repr ctorTy
--   ".data " ++ x ++ " : " ++ Kind.repr max_prec K ++ Std.Format.line
--       ++ "#𝓋" ++ Std.Format.sbracket (cs.to.fold Std.Format.nil (λ c acc => acc ++ ", " ++ Std.Format.line ++ c))
-- | .ctor x _ spTy => ".ctor " ++ x ++ " " ++ spTy.repr
-- | .odata x K =>  ".odata " ++ x ++ " " ++ K.repr max_prec
-- | .openm x spTy => ".openm " ++ x ++ " : " ++ SpineTy.repr spTy
-- | .defn x T t => ".defn " ++ x ++ " " ++ T.repr max_prec ++ t.repr max_prec
-- | .octor x spTy => ".octor " ++ x ++ SpineTy.repr spTy

-- instance instRepr_Entry : Repr Entry where
--   reprPrec e p := Entry.repr p e

def Entry.name : Entry -> String
| data x _ _ => x
| ctor x _ _ => x
| odata x _ => x
| openm x _ => x
| defn x _ _ => x
| octor x _ => x

def Entry.is_data : DataConst -> Entry -> Bool
| .cls, data _ _ _ => true
| .opn, odata _ _ => true
| _, _ => false

-- def Entry.is_ctor : Entry -> Bool
-- | ctor _ _ _ => true
-- | _ => false

-- def Entry.is_opent : Entry -> Bool
-- | odata _ _ => true
-- | _ => false

-- def Entry.is_openm : Entry -> Bool
-- | openm _ _ _ => true
-- | _ => false

-- def Entry.is_defn : Entry -> Bool
-- | defn _ _ _ => true
-- | _ => false

-- def Entry.is_instty : Entry -> Bool
-- | octor _ _ => true
-- | _ => false

def Entry.kind : Entry -> Option Kind
| data _ K _ => K
| odata _ K => K
| _ => none

def Entry.spine_type : Entry -> Option SpineTy
| ctor _ _ T => T
| openm _ T => T
| octor _ T => T
| _ => none

def Entry.ctor? (data : String) : DataConst -> Entry -> Bool
| .cls, ctor _ _ ⟨_, _, _, _, _, _, T⟩ | .opn, octor _ ⟨_, _, _, _, _, _, T⟩ =>
  match T.spine with
  | some ⟨d, _⟩ => d == data
  | none => false
| _, _ => false

-- def Entry.spctor_type : Entry -> Option Ty
-- | ctor _ _ T => T
-- | octor _ T => T
-- | openm _ _ T => T
-- | _ => none

-- def Entry.datatype : Entry -> Option Ty
-- | ctor _ _ T => T
-- | octor _ T => T
-- | _ => none

def lookup (x : String) : List Global -> Option Entry
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

def lookup_spine_type G c := lookup c G |> Option.map Entry.spine_type |> Option.getD (dflt := none)

def lookup_ctor? (G : List Global) (c : DataConst) (ctor : String) (data : Ty) : Bool :=
  match data.spine with
  | some (x, _) => lookup ctor G |> Option.map (Entry.ctor? x c) |> Option.getD (dflt := false)
  | none => false

def lookup_ctor_names (G : GlobalEnv) (T : Ty) : Option ((n : Nat) × Vec String n) := do
  let ⟨d, _⟩ <- T.spine
  match lookup d G with
  | some (.data _ _ ctors) =>
    return ⟨ctors.length, ctors.map (·.1) ⟩
  | _ => none


@[simp]
def Pattern.match : Vec Constructor m -> Pattern m' -> Bool
| .nil, .nil => true
| .cons ⟨q, m, _, n, _, k, _⟩ xs, .cons ⟨q', m', _, n', k'⟩ zs =>
  Pattern.match xs zs && q == q' && m == m' && n == n' && k == k'
| _, _ => false

def get_instance (x : String) (ctors : (Vec Constructor m)) : (G : List Global) -> Option ((m : Nat) × Pattern m × Term)
| .nil => none
| .cons (.inst (m := m) y p b) G' =>
  if x == y && Pattern.match ctors p
  then some ⟨m, p, b⟩
  else get_instance x ctors G'
| .cons _ G' => get_instance x ctors G'

def lookup_defn (G : List Global) (x : String) : Option (Ty × Term) := do
  let t <- lookup x G
  match t with
  | .defn _ T t => return ⟨T, t⟩
  | _ => none

def lookup_kind G x := lookup x G |> Option.map Entry.kind |> Option.join
-- def lookup_type G x := lookup x G |> Option.map Entry.type |> Option.get!
-- def lookup_spctor_type G x := lookup x G |> Option.map Entry.spctor_type |> Option.get!
-- def is_ctor G x := lookup x G |> Option.map Entry.is_ctor |> Option.get!
def is_data c G x := lookup x G |> Option.map (Entry.is_data c) |> Option.getD (dflt := false)
-- def is_instty G x := lookup x G |> Option.map Entry.is_instty |> Option.get!
-- def is_opent G x := lookup x G |> Option.map Entry.is_opent |> Option.get!
-- def is_openm G x := lookup x G |> Option.map Entry.is_openm |> Option.get!
-- def is_defn G x := lookup x G |> Option.map Entry.is_defn |> Option.get!

theorem lookup_name_eq :
  lookup x G = some e ->
  e.name = x := by
intro h
fun_induction lookup
cases h
simp at h; cases e <;> (simp at h; try simp [Entry.name]); simp_all
case _ ctors _ ctors' _ ih =>
  replace h := Vec.fold_or h
  cases h
  case _ h => apply ih h
  case _ h =>
    rcases h with ⟨i, h⟩
    unfold ctors' at h; simp at h;
    rw[<-h.2]; rw[<-h.1]; simp [Entry.name]
any_goals (simp at h; cases e <;> (simp at h; try simp [Entry.name]); simp_all)
any_goals (case _ ih => apply ih h)

def lookup_octor (G : GlobalEnv) (T : Ty) : Option (List String) := do
  let ⟨d, _⟩ <- T.spine
  G.filterMapM (λ g => match g with
                   | .octor n ⟨_, _, _, _, _, _, R⟩ => do let ⟨d', _ ⟩ <- R.spine
                                                          if d' == d then return (some n) else return none
                   | _ => return none)


-- def ctor_idx (G : List Global) (x : String) : Option Nat := do
--   let t <- lookup x G
--   match t with
--   | .ctor _ n _ => n
--   | _ => none

-- def ctor_ty (G : List Global) (x : String) : Option Ty := do
--   let t <- lookup_type G x
--   if is_ctor G x then return t else none

-- def ctor_count (G : List Global) (x : String) : Option Nat := do
--   let t <- lookup x G
--   match t with
--   | .data _ _ ctors => Vec.length ctors
--   | _ => .none


-- theorem lookup_type_reconstruct :
--   lookup x G = some e ->
--   e.type = some T ->
--   lookup_type G x = some T
-- := by
--   intro j1 j2
--   simp [lookup_type]; rw [j1]; simp
--   exact j2

-- theorem lookup_entry_openm_exists :
--   is_openm G x -> ∃ y T, lookup x G = .some (Entry.openm y T) := by
-- intro h
-- simp [is_openm] at h
-- generalize edef : lookup x G = e at *
-- cases e <;> simp at h
-- case _ e =>
-- cases e <;> simp [Entry.is_openm] at h
-- case _ x T => exists x; exists T

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

-- theorem is_stable_implies_not_is_openm : is_stable G x -> ¬ is_openm G x := by
--   intro h1 h2
--   simp [is_stable] at h1;
--   cases h1
--   all_goals
--     case _ h1 =>
--       have lem := lookup_entry_openm_exists h2
--       rcases lem with ⟨_, _, lem⟩
--       simp [is_ctor, is_instty] at h1; rw[lem] at h1
--       simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
-- grind_pattern is_stable_implies_not_is_openm => is_stable G x, is_openm G x

-- theorem is_stable_implies_not_is_defn : is_stable G x -> ¬ is_defn G x := by
--   intro h1 h2
--   simp [is_stable] at h1;
--   cases h1
--   all_goals
--     case _ h1 =>
--       have lem := lookup_entry_defn_exists h2
--       rcases lem with ⟨_, _, _, lem⟩
--       simp [is_ctor, is_instty] at h1; rw[lem] at h1
--       simp at h1; simp [Entry.is_ctor, Entry.is_instty] at h1
-- grind_pattern is_stable_implies_not_is_defn => is_stable G x, is_defn G x

-- theorem is_stable_implies_lookup_defn_none : is_stable G x -> lookup_defn G x = none := by
--   intro h
--   have lem := is_stable_implies_not_is_defn h
--   unfold is_defn at lem; unfold lookup_defn; simp
--   intro a h2; rw [h2] at lem; simp at lem
--   cases a <;> simp
--   simp [Entry.is_defn] at lem
-- grind_pattern is_stable_implies_lookup_defn_none => is_stable G x

-- theorem is_openm_implies_lookup_defn_none : is_openm G x -> lookup_defn G x = none := by
--   sorry
-- grind_pattern is_openm_implies_lookup_defn_none => is_openm G x

-- theorem not_stable_implies_openm_or_defn :
--   is_stable G x = false ->
--   (lookup_type G x).isSome ->
--   is_defn G x ∨ is_openm G x
-- := by
--   intro h1 h2
--   unfold is_stable at h1
--   unfold is_ctor at h1
--   unfold is_instty at h1
--   unfold lookup_type at h2
--   unfold is_defn; unfold is_openm
--   generalize zdef : lookup x G = z at *
--   cases z; simp [Option.isSome] at h2; case _ z =>
--   cases z <;> simp [Entry.type, Entry.is_ctor, Entry.is_instty] at *
--   all_goals simp [Entry.is_defn, Entry.is_openm]

-- theorem Global.lookup_unique :
--   lookup x G = t ->
--   lookup x G = t' ->
--   t = t'
-- := by
--   intro h1 h2
--   all_goals (rw[h1] at h2; exact h2)

-- theorem Global.lookup_type_unique :
--   lookup_type x G = some t ->
--   lookup_type x G = some t' ->
--   t = t' := by
-- intro h1 h2
-- all_goals (rw[h1] at h2; injection h2)

-- theorem Global.get_defn :
--   is_defn G x ->
--   ∃ T t, lookup x G = some (.defn x T t)
-- := by
--   intro h
--   unfold is_defn at h
--   generalize zdef : lookup x G = z at *
--   cases z; simp at h; case _ z =>
--   cases z <;> simp [Entry.is_defn] at h
--   simp
--   sorry

-- theorem Global.get_openm :
--   is_openm G x ->
--   ∃ T, lookup x G = some (.openm x T)
-- := by
--   sorry

end Core
