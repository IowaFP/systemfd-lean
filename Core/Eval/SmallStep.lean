import LeanSubst

import Core.Vec
import Core.Ty
import Core.Term
import Core.Global
import Core.Reduction.Definition

import Core.Util
open LeanSubst

namespace Core

@[simp]
def inline_insts (n : String) (G : List Global) (sp : List SpineElem) :=
  List.foldr (λ (x : Term) (acc : Term) => x.apply sp `+ acc) `0 (instances n G)

@[simp]
def eval_choice_mapping (G : List Global) : Term -> Option Term
| .match (.ctor2 .choice t1 t2) ps ts c =>
  return (.match t1 ps ts c `+ .match t2 ps ts c)
| .match s ps ts c => do
  let s' <- eval_choice_mapping G s
  return .match s' ps ts c

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
  if v == .choice then .none -- do not distribute choice over choice
  else return ((.ctor2 v t1 a) `+ .ctor2 v t2 a)

| .ctor2 v t (.ctor2 .choice a1 a2) =>
  return (.ctor2 v t a1) `+ (.ctor2 v t a2)

| .ctor2 v t1 t2 =>
  if v.congr1
  then match eval_choice_mapping G t1 with
       | .some t1' => return .ctor2 v t1' t2
       | .none => if v.congr2
                  then match eval_choice_mapping G t2 with
                       | .some t2' => return .ctor2 v t1 t2'
                       | .none => .none
                  else .none
  else (if v.congr2
        then match eval_choice_mapping G t2 with
             | .some t2' => return .ctor2 v t1 t2'
             | .none => .none
        else .none)

| _ => .none


@[simp]
def eval_const_folding_zero (G : List Global) : Term -> Option Term
| .match `0 _ _ _=> return `0
| .match s ps ts c => do
  let s' <- eval_const_folding_zero G s
  return .match s' ps ts c
| .guard _ `0 _ => return `0
| .guard p s t => do
  let s' <- eval_const_folding_zero G s
  return .guard p s' t
| .ctor1 _ `0 => return `0
| .ctor1 v t => do
  let t' <- eval_const_folding_zero G t
  return .ctor1 v t'

| .ctor2 .choice `0 t => return t
| .ctor2 .choice t `0 => return t

| .ctor2 v `0 _ => if v.congr1 then return `0 else .none
| .ctor2 v _ `0 => if v.congr2 then return `0 else .none

| .ctor2 v t1 t2 =>
  if v.congr1
  then match eval_const_folding_zero G t1 with
       | .some t1' => return .ctor2 v t1' t2
       | .none => if v.congr2
                  then match eval_const_folding_zero G t2 with
                       | .some t2' => return .ctor2 v t1 t2'
                       | .none => .none
                  else .none
  else (if v.congr2
        then match eval_const_folding_zero G t2 with
             | .some t2' => return .ctor2 v t1 t2'
             | .none => .none
        else .none)

| .tbind .allc _ `0 => return `0

| .tbind v t1 t2 =>
  if v.congr
  then match eval_const_folding_zero G t2 with
             | .some t2' => return .tbind v t1 t2'
             | .none => .none
  else .none

| _ => .none


@[simp]
def eval_const_folding_refl (G : List Global) : Term -> Option Term
| .match s ps ts c => do
  let s' <- eval_const_folding_refl G s
  return .match s' ps ts c
| .guard p s t => do
  let s' <- eval_const_folding_refl G s
  return .guard p s' t
| .ctor1 .sym (.ctor0 (.refl t)) => return refl! t

| .ctor1 .fst (.ctor0 (.refl (.app A _))) => return refl! A
| .ctor1 .snd (.ctor0 (.refl (.app _ B))) => return refl! B
| .ctor1 v t => do
  let t' <- eval_const_folding_refl G t
  return .ctor1 v t'
| .ctor2 .seq (.ctor0 (.refl t)) (.ctor0 (.refl t')) =>
  if t == t' then return refl! t else .none
| .ctor2 .appc (.ctor0 (.refl t)) (.ctor0 (.refl t')) => return .ctor0 (.refl (t • t'))
| .ctor2 .apptc (.ctor0 (.refl (.all _ t))) (.ctor0 (.refl t')) => return refl! (t[su t'::+0:Ty])
| .ctor2 .arrowc (.ctor0 (.refl t)) (.ctor0 (.refl t')) => return refl! (t -:> t')
| .ctor2 v t1 t2 =>
  if v.congr1
  then match eval_const_folding_refl G t1 with
       | .some t1' => return .ctor2 v t1' t2
       | .none => if v.congr2
                  then match eval_const_folding_refl G t2 with
                       | .some t2' => return .ctor2 v t1 t2'
                       | .none => .none
                  else .none
  else (if v.congr2
        then match eval_const_folding_refl G t2 with
             | .some t2' => return .ctor2 v t1 t2'
             | .none => .none
        else .none)
| .tbind .allc t (.ctor0 (.refl t')) => return refl! (∀[t] t')
| _ => .none




@[simp]
def eval_inst_beta (G : List Global) :  Term -> Option Term
| .ctor1 (.appt a) (.tbind .lamt _ t) => return t[.su a::+0 : Ty]
| .ctor1 v t => do
  let t' <- eval_inst_beta G t
  return .ctor1 v t'

| .ctor2 (.app _) (.lam _ t) a => return t[su a ::+0]
| .ctor2 (.app k) t1 t2 => do
  let t' <- eval_inst_beta G t1
  return .ctor2 (.app k) t' t2

| .ctor2 .cast t (refl! _) => t
| .ctor2 v t1 t2 =>
  if v.congr1
  then match eval_inst_beta G t1 with
       | .some t1' => return .ctor2 v t1' t2
       | .none => if v.congr2
                  then match eval_inst_beta G t2 with
                       | .some t2' => return .ctor2 v t1 t2'
                       | .none => .none
                  else .none
  else if v.congr2
                  then match eval_inst_beta G t2 with
                       | .some t2' => return .ctor2 v t1 t2'
                       | .none => .none
                  else .none

| .guard pat s t =>
  match s.spine with
  | .none => do
    let s' <- eval_inst_beta G s
    return .guard pat s' t
  | .some (s_x, s_sp) =>
    match pat.spine with
    | .some (pat_x, pat_sp) =>
      if s_x == pat_x
      then match prefix_equal pat_sp s_sp with
           | .some l => return t.apply l
           | _ => .some `0
      else .some `0
    | .none => .none

| .match (n := n) s ps' cs default => do
   let ps : Vect n (Option (String × List SpineElem)) := λ i => (ps' i).spine
   let ps <- ps.seq -- just fail if patterns are not of the correct shape
   let p_pats : Vect n String := λ i => (ps i).1
   let p_sps : Vect n (List SpineElem) := λ i => (ps i).2
   match eval_inst_beta G s with
   | .some s' => return .match s' ps' cs default
   | .none => match s.spine with
           | .none => .none -- stuck term, cannot evaluate and not in neutral form
           | .some (s_x, s_sp) => do
               match (p_pats.indexOf s_x) with
               | .none => return default -- catch all case
               | .some i => do
                       let pat_sp : List SpineElem := (p_sps i)
                       match prefix_equal pat_sp s_sp with
                       | .some p => return (cs i).apply p
                       | .none => none -- stuck term

| t => match t.spine with
       | .some (x, sp) =>
         if is_defn G x
         then do
              let t <- lookup_defn G x
              return t.apply sp
         else if is_openm G x
              then return (inline_insts x G sp)
              else .none
       | .none => .none

@[simp]
def eval (G : List Global) (t : Term) : Option Term :=
match eval_choice_mapping G t with
| .some t => return t
| none =>
  match eval_const_folding_zero G t with
  | .some t => .some t
  | .none => match eval_const_folding_refl G t with
             | .some t => .some t
             | .none => eval_inst_beta G t

end Core
