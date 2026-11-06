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
  List (String × List Nat × Nat) -> -- FDS
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
    -- ++ "|" ++ fds.repr max_prec
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
  List (String × List Nat × Nat) ->
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

  That is only C a is scrutinizatble

 -/
--

def spine_type_type : Core.SpineTy -> Core.Ty
| ⟨_, Ks1, _, Ks2, _, Ts, R⟩ => ((Ts.reverse.foldl (Core.Ty.arrow · ·) R).genTy Ks2).genTy Ks1


def mk_method_om (cls : String) (cls_params : Vec Core.Kind kc) (R : Core.SpineTy) : Core.SpineTy :=
  let ski := (List.range cls_params.length)
  ⟨kc, cls_params, 0, #(), 1,  #((gt#cls).mkApps_nats ski.reverse), spine_type_type R⟩


-- Determiners are the parameters that remain fixed
-- Non determiners are the parameters that change
-- Determinant parameter is the one that we build the equality out of


-- def non_determiners (cls_params : Vec Core.Kind kc) : List (Fin kc) -> (n : Nat) ×' Vec Core.Kind n
-- | .nil => ⟨kc, cls_params⟩
-- | .cons x xs =>

--   let ⟨_, t⟩ := cls_params.eraseIdx x
--   non_determiners t xs

-- #eval (non_determiners #(★, ★ -:> ★, ★ -:> ★, ★) [2]).snd

def non_determiners (cls_params : List Core.Kind) : List Nat -> List Core.Kind
| .nil => cls_params
| .cons x xs =>
  let cls_params' := cls_params.eraseIdx x
  non_determiners cls_params' xs

#eval (non_determiners [★, ★ -:> ★, ★ -:> ★, ★] [2])


-- Pre-conditions : Determiners.length < kc
-- Determiners are sorted
-- F t u v | t -> u
-- Determiners are [t]
-- Non-determiners are [v]
-- Determinant is v

def mk_fd_om (cls : String) (cls_params : Vec Core.Kind kc) (determiners : List (Fin kc)) (determinant : Fin kc)
  : Core.SpineTy :=

  let Δ' := cls_params.list

  let Δ' := non_determiners Δ' determiners
  let ⟨kc', Δ'⟩ := Vec.from_list Δ'

  let new_params_length := kc'

  let cls_ty := ((gt#cls).mkApps_nats (List.range cls_params.length).reverse)⟨Ren.add Core.Ty new_params_length⟩
  let cls_ty' := (gt#cls).mkApps_nats (List.range cls_params.length).reverse


  let R := t#(determinant + new_params_length) ~[cls_params[determinant]]~ t#0
  ⟨kc' + kc, cls_params ++ Δ', 0, #(), 2, #(cls_ty, cls_ty'), R⟩

#eval mk_fd_om "F" #(★, ★ -:> ★, ★) [2] 0
-- ⟨4, #(★, ★ -:> ★, ★) ++ #(★) ++ #(★), F t#4 t#3 t#2, F t#4 t#1 #0, #2 ~[★]~ t#0⟩

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
  -- let fds_mb : Option (String × (n : Nat) × Vec (Fin kc) (n + 1) × Fin kc) := fds.find? (λ ⟨fdn, _, _, _⟩ => x == fdn)
  if ms.isSome then ms
  else if scs.isSome then scs
  -- else if fds.isSome then fds
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

end Surface
