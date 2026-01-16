import LeanSubst
import Core.Vec
import Core.Ty
import Core.Term

open LeanSubst

inductive Global : Type where
| data : String -> Kind -> Vec (String × Ty) n -> Global
| opent : String -> Kind -> Global
| openm : String -> Ty -> Global
| «let» : String -> Ty -> Term -> Global
| inst : String -> Term -> Global
| instty : String -> Ty -> Global

def lookup_kind (x : String) : List Global -> Option Kind
| [] => none
| .cons (.data n K _) t
| .cons (.opent n K) t =>
  if n == x then K else lookup_kind x t
| .cons _ t => lookup_kind x t

def lookup_type (x : String) : List Global -> Option Ty
| [] => none
| .cons (.data _ _ ctors) t =>
  sorry
| .cons (.openm n A) t
| .cons (.let n A _) t
| .cons (.instty n A) t =>
  if n == x then A else lookup_type x t
| .cons _ t => lookup_type x t

def instances (x : String) : List Global -> Option (List Term) := sorry

def is_ctor : List Global -> String -> Bool := sorry

def is_datatype : List Global -> String -> Bool := sorry

def is_instty : List Global -> String -> Bool := sorry

def is_opent : List Global -> String -> Bool := sorry

def is_openm : List Global -> String -> Bool := sorry

def ctor_idx : List Global -> String -> Option (Fin n) := sorry

def is_stable : List Global -> String -> Bool := sorry
