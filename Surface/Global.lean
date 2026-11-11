import LeanSubst
import Common.Vec
import Lilac
import Surface.Term
import Core.Term

open LeanSubst
open Lilac

namespace Surface

inductive Global where
| data : {n : Nat} -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Global
| defn : String -> Core.Ty -> Term -> Global
| classDecl : {kc : Nat} ->
  String -> Vec Core.Kind kc ->
  List (String × List (Fin kc) × Fin kc) -> -- FDS
  List (String × String × List (Fin kc)) -> -- SCS
  List (String × Core.SpineTy) -> -- methods
  Global

| instDecl : String -> Core.SpineTy -> List (String × Term) -> Global


def Global.repr (_ : Nat) : (a : Global) -> Std.Format
| .data (n := n) s K ctors =>
  let cs : Fun.Vec Std.Format n := λ i =>
    let ctorN := (Vec.to ctors i).1
    let ctorTy := (Vec.to ctors i).2
    ctorN ++ " : " ++ Core.SpineTy.repr ctorTy ++ Std.Format.line
  (Std.Format.text ".data ") ++ (Std.Format.text s) ++ " : "
    ++ (K.repr max_prec) ++ " where" ++ Std.Format.line ++
    Std.Format.nest 4  (Std.Format.align true ++ cs.to.fold_format)
| .defn n T t =>
  ".defn " ++ n ++ " " ++ (T.repr max_prec)
  ++ Std.Format.nest 4 (Std.Format.align true ++ t.repr max_prec)
| .classDecl s Ks fds scs methods =>
  ".class " ++ s ++ " : " ++ Ks.repr max_prec ++ " where" ++ Std.Format.line
    ++ "|"  ++ scs.repr max_prec
    ++ "|" ++ fds.repr max_prec
    ++ "|" ++ Std.Format.line ++ (methods.repr max_prec)
| instDecl i_name spTy methods =>
  (Std.Format.text ".inst ") ++ i_name ++ " : " ++ "⟨" ++ spTy.repr ++ "⟩"
    ++ Std.Format.line ++ Std.Format.nest 4 (Std.Format.align true ++ methods.repr max_prec)

@[simp]
instance instRepr_Global : Repr (Global) where
  reprPrec a p := Global.repr p a

@[simp]
abbrev GlobalEnv := List (Global)

inductive Entry : Type where
| data : {n : Nat} -> String -> Core.Kind -> Vec (String × Core.SpineTy) n -> Entry
| ctor : String -> Nat -> Core.SpineTy -> Entry
| defn : String -> Core.Ty -> Term -> Entry
| odata : {n : Nat} -> String -> Vec Core.Kind n ->
  List (String × List (Fin n) × Fin n) ->
  List (String × String × List (Fin kc)) ->
  List (String × Core.SpineTy) -> Entry
| octor : String -> Core.SpineTy -> Entry
| openm : String -> Core.SpineTy -> Entry

def Entry.is_data : Core.DataConst -> Entry -> Bool
| .cls, .data _ _ _ => true
| .opn, .odata _ _ _ _ _ => true
| _, _ => false

def Entry.is_ctor : Entry -> Bool
| ctor _ _ _ => true
| _ => false

def Entry.is_odata : Entry -> Bool
| odata _ _ _ _ _ => true
| _ => false

def Entry.is_openm : Entry -> Bool
| openm _ _ => true
| _ => false

def Entry.is_defn : Entry -> Bool
| defn _ _ _ => true
| _ => false

def Entry.kind : Entry -> Option Core.Kind
| data _ K _ => K
| odata _ Ks _ _ _ => Core.Kind.mk_cls_kind Ks
| _ => none

def mk_superclass_om (cls : String) (cls_params : Vec Core.Kind kc) (sc : String) (sc_params : List (Fin kc)) : Core.SpineTy :=
  let cls_ty := (gt#cls).mkApps_nats (List.range cls_params.length).reverse
  let sc_ty := (gt#sc).mkApps_nats sc_params
  ⟨kc, cls_params, 0, #(), 1, #(cls_ty), sc_ty⟩


/-
  if the class declaration in surface is as follows

    class C a where c :: ∀ t u, D (t a) => t a -> u a -> u a

  the open method associated with this will be:

    openm c :: ∀a. C a = (∀ t u, D (t a) => t a -> u a -> u a)

  That is only `C a` can be scrutinized.

 -/

def spine_type_type : Core.SpineTy -> Core.Ty
| ⟨_, Ks1, _, Ks2, _, Ts, R⟩ => ((Ts.reverse.foldl (Core.Ty.arrow · ·) R).genTy Ks2).genTy Ks1


def mk_method_om (cls : String) (cls_params : Vec Core.Kind kc) (R : Core.SpineTy) : Core.SpineTy :=
  let ski := (List.range cls_params.length)
  ⟨kc, cls_params, 0, #(), 1,  #((gt#cls).mkApps_nats ski.reverse), spine_type_type R⟩


-- Determiners are the parameters that remain fixed
-- Non determiners are the parameters that change
-- Determinant parameter is the one that we build the equality out of


-- Pre-conditions : Determiners.length < kc
-- Determiners are sorted
-- F t u v | t -> u
-- Determiners are [t]
-- Non-determiners are [v]
-- Determinant is v

def mk_fd_om (cls : String) (cls_params : Vec Core.Kind kc) (determiners : List (Fin kc)) (determinant : Fin kc)
  : Core.SpineTy :=

  let is_determiner : Nat -> Bool := λ x => (determiners.map (λ x => x.toNat)).contains x
  let is_determinant : Nat -> Bool := λ x => x == determinant.toNat

  let cls_params' := (Vec.zipIdx cls_params.reverse).list
  let cls_params' := cls_params'.filter (λ x => !is_determiner x.2)
  let cls_params' := (cls_params'.map (·.fst)).reverse
  let ⟨kc', cls_params'⟩ := Vec.from_list cls_params'

  let cls_ty := ((gt#cls).mkApps_nats (List.range kc).reverse)⟨Ren.add Core.Ty kc'⟩

  let idx_fiddling (idxs : List Nat) (init : Nat) : (List Nat × Nat × Nat) :=
    idxs.foldl (init := ([], init, 0)) (λ acc x =>
      if is_determiner x
      then (acc.1 ++ [x + kc'], acc.2.1, acc.2.2)
      else (acc.1 ++ [acc.2.1], acc.2.1 - 1, if is_determinant x then acc.2.1 else acc.2.2))

  let idxs := idx_fiddling ((List.range kc).reverse) (kc' - 1)

  let cls_ty' := (gt#cls).mkApps_nats idxs.1


  let R := t#(determinant + kc') ~[cls_params.reverse[determinant]]~ t#idxs.2.2

  ⟨kc' + kc, cls_params ++ cls_params', 0, #(), 2, #(cls_ty, cls_ty'), R⟩

#eval mk_fd_om "F" #(★, ★ -:> ★, ★) [2] 0
-- ⟨5, #(★, ★ -:> ★, ★) ++ #(★) ++ #(★), F t#4 t#3 t#2, F t#4 t#1 #0, #2 ~[★]~ t#0⟩
#eval mk_fd_om "F" #(★ -:> ★, ★) [0] 1
-- ⟨5, #(★ -:> ★, ★, ★ -:> ★), #(F `2 `1 , F `0 `1), `2 ~[★ -:> ★]~ `0⟩


def lookup (x : String) : GlobalEnv -> Option (Entry)
| [] => none
| .cons (.data y K ctors) tl =>
  let ctors' := Vec.map
    (λ ((z, A), i) => if x == z then some (Entry.ctor z i A) else none)
    (Vec.zipIdx ctors)
  if x == y then return .data y K ctors
  else ctors'.foldr (init := lookup x tl) Option.or
| .cons (.defn y a b) tl =>
  if x == y then return .defn y a b else lookup x tl
| .cons (.classDecl (kc := kc) y Ks fds scs ms) tl =>
  if x == y then return .odata y Ks fds scs ms else

  let ms_mb : Option (String × Core.SpineTy) := ms.find? (λ (mn, _) => x == mn)
  let ms := ms_mb.map (λ (x, mn) => .openm x (mk_method_om y Ks mn))
  -- TODO Extensions for fundeps
  let scs_mb : Option (String × String × List (Fin kc)) := scs.find? (λ (sc, _, _) => x == sc)
  let scs := scs_mb.map (λ (scn, cls, tys) => Entry.openm scn (mk_superclass_om y Ks cls tys))

  let fds_mb : Option (String × List (Fin kc) × Fin kc) := fds.find? (λ ⟨fdn, _, _, _⟩ => x == fdn)
  let fd := fds_mb.map (λ (fdn, dms, det) => Entry.openm fdn (mk_fd_om y Ks dms det))

  if ms.isSome then ms
  else if scs.isSome then scs
  else if fd.isSome then fd
  else lookup x tl
| .cons (.instDecl s spTy _) tl =>
  if x == s then return .octor s spTy
  else lookup x tl

def lookup_kind (G : GlobalEnv) (x : String) : Option Core.Kind := lookup x G |> Option.map Entry.kind |> Option.get!
def is_data c G x := lookup x G |> Option.map (Entry.is_data c) |> Option.getD (dflt := false)

def Entry.name : Entry -> String
| data x _ _ => x
| ctor x _ _ => x
| octor x _ => x
| openm x _ => x
| defn x _ _ => x
| odata x _ _ _ _ => x


theorem lookup_name_agrees : lookup x G = some e -> e.name = x := by
  intro h; fun_induction lookup <;> simp_all
  all_goals try solve | subst h; simp [Entry.name]
  case _ n y K ctors tl ctors' h2 ih =>
    generalize zdef : lookup x tl = z at *
    replace h := Vec.foldr_or h
    cases h
    case _ h =>
      rcases h with ⟨j, h⟩
      subst ctors'; simp at h
      rcases h with ⟨h1, h3⟩; subst h1
      subst e; simp[Entry.name]
    case _ h =>
      apply ih h.2
  case _ ms_mb ms _ =>
    simp [ms, ms_mb] at h; rcases h with ⟨a, b, h, h1⟩
    simp [<-h1, Entry.name]; subst e; simp [List.find?_eq_some_iff_getElem] at h; symm; apply h.1
  case _ scs_mb scs _ _ =>
    simp [scs, scs_mb] at h; rcases h with ⟨a, b, h, h1, h2⟩
    simp [<-h2, Entry.name]; simp [List.find?_eq_some_iff_getElem] at h1
    rcases h1 with ⟨h1, _⟩; symm; apply h1
  case _ fds_mb fds _ _ _ =>
    simp [fds_mb, fds] at h; rcases h with ⟨a, b, h, h1, h2⟩
    simp [<-h2, Entry.name]; simp [List.find?_eq_some_iff_getElem] at h1
    rcases h1 with ⟨h1, _⟩; symm; apply h1

end Surface
