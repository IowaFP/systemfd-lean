import LeanSubst

import Core.Vec
import Core.Ty
import Core.Term
import Core.Global

open LeanSubst

@[simp]
def get_insts (n : String) :  List Global -> List Term
| [] => []
| .cons (.inst n' t) G =>
  if n == n'
  then t :: (get_insts n G)
  else get_insts n G
| .cons _ G => get_insts n G

@[simp]
def inline_insts (n : String) (G : List Global) (sp : List SpineElem) :=
  List.foldr (λ (x : Term) (acc : Term) => x.apply sp `+ acc) `0 (get_insts n G)

@[simp]
def eval_choice_mapping (G : List Global) : Term -> Option Term
| .match p (.ctor2 .choice t1 t2) ts =>
  return (.match p t1 ts `+ .match p t2 ts)
| .match p s ts => do
  let s' <- eval_choice_mapping G s
  return .match p s' ts

| .guard  p (.ctor2 .choice s1 s2) t =>
  return (.guard p s1 t `+ .guard p s2 t)
| .guard p s t => do
  let s' <- eval_choice_mapping G s
  return .guard p s' t
| .ctor1 v (.ctor2 .choice t1 t2) =>
  return .ctor1 v t1 `+ .ctor1 v t2
| .ctor1 v t =>  do
  let t' <- eval_choice_mapping G t
  return .ctor1 v t'

| .ctor2 .choice t1 t2 =>
  match eval_choice_mapping G t1 with
  | .some t1' => return t1' `+ t2
  | .none => match eval_choice_mapping G t2 with
             | .some t2' => return t1 `+ t2'
             | .none => .none

| .ctor2 v (.ctor2 .choice t1 t2) a =>
  if v == .choice then .none
  else return ((.ctor2 v t1 a) `+ .ctor2 v t2 a)

| .ctor2 v t (.ctor2 .choice a1 a2) =>
  return (.ctor2 v t a1) `+ (.ctor2 v t a2)

| _ => .none

@[simp]
def eval_congr (G : List Global) : Term -> Option Term
| .ctor2 .app t1 t2 =>
  match eval_congr G t1 with
  | .some t1' => return t1' • t2
  | .none => .none

| .ctor1 (.appt τ) t =>
  match eval_congr G t with
  | .some t' => return t' •[ τ ]
  | .none => .none

| .ctor2 .choice t1 t2 => do
  match eval_congr G t1 with
  | .some t1' => t1' `+ t2
  | .none => match eval_congr G t2 with
             | .some t2' => t1 `+ t2'
             | .none => .none

| .match pat s t =>
    match eval_congr G s with
    | .some s' => return .match pat s' t
    | .none => .none

| .guard pat s t =>
    match eval_congr G s with
    | .some s' => return .guard pat s' t
    | .none => .none

| _ => .none

@[simp]
def eval_inst_beta (G : List Global) :  Term -> Option Term
| .ctor1 (.appt a) (.tbind .lamt _ t) => return t[.su a::+0 : Ty]
| .ctor1 (.appt a) t => do
  let t' <- eval_inst_beta G t
  return .ctor1 (.appt a) t'

| .ctor2 .app (.lam _ t) a =>
  return t[su a ::+0]
| .ctor2 .app t1 t2 => do
  let t' <- eval_inst_beta G t1
  return .ctor2 .app t' t2

| .ctor2 .cast t (refl! _) => t

| .ctor2 .choice `0 t => return t
| .ctor2 .choice t `0 => return t

| .guard pat s t =>
  match s.spine with
  | .none => .some `0
  | .some (s_x, s_sp) =>
    match pat.spine with
    | .some (pat_x, pat_sp) =>
      if s_x == pat_x
      then match Spine.prefix_equal pat_sp s_sp with
           | .some l => return t.apply l
           | _ => .some `0
      else .some `0
    | .none => .none
| t => match t.spine with
       | .some (x, sp) => return (inline_insts x G sp)
       | .none => .none

@[simp]
def eval (G : List Global) (t : Term) : Option Term :=
match eval_choice_mapping G t with
| .some t => return t
| none =>
  match eval_congr G t with
  | .some t => .some t
  | .none => eval_inst_beta G t
