import Common.Vec
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
    ctorN ++ " : " ++ SpineTy.repr ctorTy ++ Std.Format.line
  ".data " ++ s ++ " : " ++ Kind.repr max_prec K ++ " where " ++ Std.Format.line ++
      Std.Format.nest 4 (Std.Format.align true ++ cs.to.fold_format)
| .odata n K => ".odata " ++ n ++ " " ++ K.repr max_prec
| .openm n ty => ".openm " ++ n ++ " : " ++ SpineTy.repr ty
| .defn n T t =>
  ".defn " ++ n ++ " " ++ T.repr max_prec ++ Std.Format.line
  ++ Std.Format.nest 4 (Std.Format.align true ++ t.repr max_prec)
| .inst n p t => ".inst " ++ n ++ " " ++ p.repr ++ " => " ++ t.repr max_prec
| .octor n ty => ".octor " ++ n ++ " " ++ SpineTy.repr ty


@[simp]
instance instRepr_Global : Repr Global where
  reprPrec a p := Global.repr p a

@[simp]
abbrev GlobalEnv := List Global

inductive Entry : Type where
| data : {n : Nat} -> String -> Kind -> Vec (String × SpineTy) n -> Entry
| ctor : String -> Nat -> SpineTy -> Entry
| odata : String -> Kind -> Entry
| openm : String -> SpineTy -> Entry
| defn : String -> Ty -> Term -> Entry
| octor : String -> SpineTy -> Entry

def Entry.repr (_ : Nat) : Entry -> Std.Format
| .data (n := n) x K ctors =>
  let cs : Fun.Vec Std.Format n := λ i =>
    let ctorN := (Vec.to ctors i).1
    let ctorTy := (Vec.to ctors i).2
    ctorN ++ SpineTy.repr ctorTy
  ".data " ++ x ++ " : " ++ Kind.repr max_prec K ++ " where " ++ Std.Format.line ++
      Std.Format.nest 4 (Std.Format.align true ++ cs.to.fold_format)
| .ctor x _ spTy => ".ctor " ++ x ++ " " ++ spTy.repr
| .odata x K =>  ".odata " ++ x ++ " " ++ K.repr max_prec
| .openm x spTy => ".openm " ++ x ++ " : " ++ SpineTy.repr spTy
| .defn x T t => ".defn " ++ x ++ " " ++ T.repr max_prec ++ t.repr max_prec
| .octor x spTy => ".octor " ++ x ++ SpineTy.repr spTy

instance instRepr_Entry : Repr Entry where
  reprPrec e p := Entry.repr p e

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

def Entry.kind : Entry -> Option Kind
| data _ K _ => K
| odata _ K => K
| _ => none

def Entry.spine_type : SpCtorVariant -> Entry -> Option SpineTy
| .data .cls, ctor _ _ T => T
| .openm, openm _ T => T
| .data .opn, octor _ T => T
| _, _ => none

def Entry.ctor? (data : String) : DataConst -> Entry -> Bool
| .cls, ctor _ _ ⟨_, _, _, _, _, _, T⟩ | .opn, octor _ ⟨_, _, _, _, _, _, T⟩ =>
  match T.spine with
  | some ⟨d, _⟩ => d == data
  | none => false
| _, _ => false

def lookup (x : String) : List Global -> Option Entry
| [] => none
| .cons (.data _ y K ctors) tl =>
  let ctors' := Vec.map
    (λ ((z, A), i) => if x == z then some (Entry.ctor z i A) else none)
    (Vec.zipIdx ctors)
  if x == y then return .data y K ctors
  else Vec.foldr Option.or (lookup x tl) ctors'
| .cons (.odata y a) tl =>
  if x == y then return .odata y a else lookup x tl
| .cons (.openm y a) tl =>
  if x == y then return .openm y a else lookup x tl
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.inst _ _ _) tl => lookup x tl
| .cons (.octor y a) tl =>
  if x == y then return .octor y a else lookup x tl

def lookup_spine_type d G c := lookup c G |> Option.map (Entry.spine_type d) |> Option.getD (dflt := none)

def lookup_ctor? (G : List Global) (c : DataConst) (ctor : String) (data : Ty) : Bool :=
  match data.spine with
  | some (x, _) => lookup ctor G |> Option.map (Entry.ctor? x c) |> Option.getD (dflt := false)
  | none => false

def lookup_octors (T : String) : (G : GlobalEnv)  -> Option (List String)
  | .nil => some []
  | .cons g gs => do
    let cs <- lookup_octors T gs
    match g with
    | .octor n ⟨_, _, _, _, _, _, R⟩ => do
      let ⟨d', _ ⟩ <- R.spine
      if d' == T then n :: cs else cs
    | _ => return cs


def lookup_ctor_names (G : GlobalEnv) (T : Ty) : Option ((n : Nat) × Vec String n) := do
  let ⟨d, _⟩ <- T.spine
  match lookup d G with
  | some (.data _ _ ctors) =>
    return ⟨ctors.length, ctors.map (·.1)⟩
  | some (.odata _ _) => do
    let ocs <- lookup_octors d G
    return Vec.from_list ocs
  | _ => none


@[simp]
def pattern_match : Vec Constructor m -> Pattern m -> Bool
| .nil, .nil => true
| .cons ⟨q, m, _, n, _, k, _⟩ xs, .cons ⟨q', m', _, n', k'⟩ zs =>
  pattern_match xs zs && q == q' && m == m' && n == n' && k == k'
| _, _ => false

def check_instance_eq (m n : Nat) (x y : String) (ctors : Vec Constructor m) (pat : Pattern n) : Bool :=
  if h : x == y && m == n
  then by {
    simp at h; rcases h with ⟨h1, h2⟩; subst h2
    apply pattern_match ctors pat
  }
  else false

def instance_idx? (x : String) (ctors : Vec Constructor m) (G : List Global) : Option Nat :=
  G.findIdx? (λ g => match g with
  | .inst (m := n) y p _ => check_instance_eq m n x y ctors p
  | _ => false )

def get_instance_from_idx (x : String) (ctors : Vec Constructor m) (G : GlobalEnv) (i : Nat)
  : Option (Nat × (m : Nat) × Pattern m × Term) :=
    match G[i]? with
    | some (Global.inst (m := n) y p b) =>
      if check_instance_eq m n x y ctors p
      then by {
        if h : m == n
        then simp at h; cases h -- TODO: abstract this as a predicate
             if e : pattern_match ctors p
             then apply some ⟨i, ⟨m, p, b⟩⟩
             else apply none
        else apply none
      }
      else none
    | _ => none


def get_instance (x : String) (ctors : (Vec Constructor m)) (G : GlobalEnv):
  Option (Nat × (m : Nat) × Pattern m × Term) :=
  let midx : Option Nat := instance_idx? x ctors G
  (midx.map (get_instance_from_idx x ctors G)).join



def lookup_defn (G : List Global) (x : String) : Option (Ty × Term) := do
  let t <- lookup x G
  match t with
  | .defn _ T t => return ⟨T, t⟩
  | _ => none

def lookup_kind G x := lookup x G |> Option.map Entry.kind |> Option.join
def is_data c G x := lookup x G |> Option.map (Entry.is_data c) |> Option.getD (dflt := false)


theorem lookup_append_none {G1 G2 : List Global} :
  Core.lookup x (G1 ++ G2) = none <->
  (Core.lookup x G1 = none ∧ Core.lookup x G2 = none)
:= by
  apply Iff.intro
  intro h1
  induction G1 generalizing G2 <;> simp [lookup] at *
  apply h1
  case _ hd tl ih =>
    cases hd <;> simp [lookup] at *
    case data s _ _ =>
      split at h1 <;> try simp at h1
      simp [Vec.foldr_or_val_eq_none] at h1;
      rcases h1 with ⟨h1, h2⟩
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e), Vec.foldr_or_val_eq_none];
      apply And.intro
      grind
      replace ih := ih h1; apply ih.2
    all_goals try (case _ s _ =>
      split at h1 <;> try simp at h1
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e)];
      apply ih h1)
    case _ s _ _ =>
      split at h1 <;> try simp at h1
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e)];
      apply ih h1
    case inst => apply ih h1

  intro h1; rcases h1 with ⟨h1, h2⟩
  induction G1 generalizing G2 <;> simp at *
  apply h2
  case _ hd tl ih =>
    cases hd <;> simp [lookup] at *
    case data s _ _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e), Vec.foldr_or_val_eq_none];
        simp [Vec.foldr_or_val_eq_none] at h1; rcases h1 with ⟨h1, h3⟩
        apply And.intro
        apply ih h1 h2
        apply h3
    all_goals try (case _ s _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e)]; apply ih h1 h2)
    case defn s _ _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e)]; apply ih h1 h2
    case inst => apply ih h1 h2

theorem lookup_append_weaken_right {G1 G2 : List Global} {e : Entry} :
  Core.lookup x G1 = some e -> Core.lookup x (G1 ++ G2) = some e
:= by
  intro h
  induction G1
  simp [lookup] at h
  case _ hd tl ih =>
    have lem : (hd :: tl ++ G2) = hd :: (tl ++ G2) := by grind
    simp [lem]; clear lem
    cases hd
    · simp [lookup] at h; split at h <;> try simp at h
      case _ e => subst x; simp [lookup]; apply h
      case _ e =>
      simp [lookup, e];
      simp [Vec.foldr_or_val_some]; simp [Vec.foldr_or_val_some] at h;
      cases h
      case _ h => apply Or.inl; apply h
      case _ h =>
        apply Or.inr; apply And.intro;
        apply ih h.1
        apply h.2
    case _ s _ =>
      simp [lookup] at h; split at h <;> try simp at h
      subst x; simp [lookup]; apply h
      have e : (x = s) = False := by grind
      simp [lookup, e]; apply ih h
    case _ s _ =>
      simp [lookup] at h; split at h <;> try simp at h
      subst x; simp [lookup]; apply h
      have e : (x = s) = False := by grind
      simp [lookup, e]; apply ih h
    case _ s _ _ =>
      simp [lookup] at h; split at h <;> try simp at h
      subst x; simp [lookup]; apply h
      have e : (x = s) = False := by grind
      simp [lookup, e]; apply ih h
    case _ => simp [lookup]; simp [lookup] at h; apply ih h
    case _ s _ =>
      simp [lookup] at h; split at h <;> try simp at h
      subst x; simp [lookup]; apply h
      have e : (x = s) = False := by grind
      simp [lookup, e]; apply ih h

theorem lookup_append_weaken_left {G1 G2 : List Global} {e : Entry} :
  Core.lookup x G1 = none -> Core.lookup x G2 = some e -> Core.lookup x (G1 ++ G2) = some e
:= by
  intro h1 h2
  induction G1 generalizing G2 <;> simp at *
  apply h2
  case _ hd tl ih =>
    have lem : hd :: tl = [hd] ++ tl := by grind
    rw[lem] at h1; rw [lookup_append_none] at h1
    rcases h1 with ⟨h1, h3⟩
    replace ih := ih h3 h2
    cases hd <;> simp [Core.lookup] at *
    case _ s _ ctors =>
      split at h1 <;> try simp at h1
      simp [Vec.foldr_or_val_eq_none] at h1;
      have e : (x = s) = False := by grind
      simp [e, Vec.foldr_or_val_some]; apply Or.inr; apply And.intro
      apply ih; intro i h;
      generalize zdef : Vec.map (fun x_1 => if x = x_1.1.fst then some (Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none) ctors.zipIdx = z at *
      have lem : z[i] = z[i] := rfl
      conv at lem =>
        rhs
        rw[<-zdef]
      simp at lem
      split at lem
      replace h1 := h1 z[i] Vec.getElem_mem; simp [h1] at lem
      contradiction
    all_goals try (case _ s _ =>
      have e : (x = s) = False := by grind
      simp [e]; apply ih)
    case _ s _ _ =>
      have e : (x = s) = False := by grind
      simp [e]; apply ih
    apply ih


theorem lookup_append_some_mpr {G1 G2 : List Global} {e : Entry} :
  Core.lookup x G1 = some e ∨ (Core.lookup x G1 = none ∧ Core.lookup x G2 = some e) ->
  Core.lookup x (G1 ++ G2) = some e
:= by
  intro h; cases h
  case _ h => apply lookup_append_weaken_right h
  case _ h =>
  rcases h with ⟨h1, h2⟩
  apply lookup_append_weaken_left h1 h2


theorem lookup_none_strengthen {g} {G} :
  lookup x (g :: G) = none ->
  lookup x G = none
:= by
  intro h
  cases g <;> simp [lookup] at h
  all_goals try (
    split at h <;> try simp at h
    · apply h)
  split at h <;> try simp at h
  case _ s _ _ _ =>
    simp [Vec.foldr_or_val_eq_none] at h
    apply h.1
  apply h


theorem lookup_none_idx_some_contra {G : GlobalEnv} {i : Nat} :
  G[i]? = some (Core.Global.openm mn τ) ->
  Core.lookup mn G = none ->
  False
:= by
  intro h1 h2
  simp [List.getElem?_eq_some_iff] at h1
  rcases h1 with ⟨hi, h1⟩
  induction G generalizing i <;> cases i
  cases hi
  cases hi
  case _ hd tl ih =>
    simp at h1; cases hd <;> simp at *
    rcases h1 with ⟨e1, e2⟩; subst e1; subst e2
    simp [lookup] at h2
  case _ hd tl ih i =>
    simp at hi h1;
    replace h2 := lookup_none_strengthen h2
    apply ih h2 hi h1


theorem lookup_some_if_idx_some {G : GlobalEnv} {i : Nat} {mths : List (String × Core.SpineTy) }:
  List.map (λ x => Core.Global.openm x.1 x.2) mths = G ->
  G[i]? = some (Core.Global.openm mn τ) ->
  (∀ (j : Nat) mn' τ, j < i -> G[j]? = some (Core.Global.openm mn' τ) -> mn ≠ mn') ->
  Core.lookup mn G = some (Core.Entry.openm mn τ)
:= by
  intro h1 h2 h3;
  induction mths generalizing G i <;> (simp at *)
  subst G; simp [lookup]; cases h2
  case _ hd tl ih =>
    rw[<-h1]; simp[lookup]; split
    case _ e =>
      subst mn;
      cases i
      simp [<-h1] at h2; simp [h2]
      case _ i =>
        simp [<-h1] at h2; replace h3 := h3 0 hd.1 hd.2 (by simp)
        simp [<-h1] at h3
    case _ e =>
    simp [<-h1] at h2;
    cases i
    simp at h2; rcases h2 with ⟨e1, e2⟩; subst mn; contradiction
    case _ i =>
      simp at h2;
      replace ih := @ih (List.map (λ x => Global.openm x.1 x.2) tl) i
      apply ih
      rfl
      simp [h2]
      grind

theorem lookup_none_if_idx_some {G : GlobalEnv} {mn : String} {mths : List (String × Core.SpineTy)}:
  List.map (λ x => Core.Global.openm x.1 x.2) mths = G ->
  (∀ (j : Nat) mn' τ, G[j]? = some (Core.Global.openm mn' τ) -> mn ≠ mn') ->
  Core.lookup mn G = none
:= by
  intro h1 h2;
  induction mths generalizing G <;> (simp at *;  subst G; simp [lookup])
  case _ hd tl ih =>
  split
  case _ e => subst e; replace h2 := h2 0 hd.1 hd.2 (by simp); contradiction
  apply ih;
  intro j mn' τ h;
  replace h2 := h2 (j + 1) mn' τ (by simp; apply h)
  apply h2



theorem lookup_some_then_idx_some {G : GlobalEnv} :
  Core.lookup mn G = some (Core.Entry.openm mn τ) ->
  ∃ i : Nat, G[i]? = some (Core.Global.openm mn τ)
:= by
  intro h;
  induction G <;> simp at *
  case _ => simp [Core.lookup] at h
  case _ hd tl ih =>
  cases hd
  case data s _ ctors =>
    simp [Core.lookup] at h
    split at h <;> try simp at *
    simp [Vec.foldr_or_val_some] at h;
    rcases h with ⟨h1, h2⟩
    replace ih := ih h1; rcases ih with ⟨i, ih⟩
    exists i+1
  all_goals try (case _ =>
    simp [Core.lookup] at h
    split at h <;> try simp at *
    replace ih := ih h; rcases ih with ⟨i, ih⟩
    exists i+1)
  case _ =>
    simp [Core.lookup] at h
    split at h <;> try simp at *
    rcases h with ⟨h1, h2⟩; subst h1; subst h2; exists 0
    replace ih := ih h; rcases ih with ⟨i, ih⟩
    exists i + 1
  case _ =>
    simp [lookup] at h;
    replace ih := ih h; rcases ih with ⟨i, ih⟩
    exists i+1


end Core
