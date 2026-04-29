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
def eval_const_folding_refl (G : List Global) : Term -> Option Term
| .mtch _ _ s ps ts c => do
  let s' <- eval_const_folding_refl G s
  return .match n s' ps ts c
-- | .guard p s t => do
--   let s' <- eval_const_folding_refl G s
--   return .guard p s' t
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

| .match (n := n) s ps cs default =>
   match eval_inst_beta G s with
   | some s' => return .match n s' ps cs default
   | none => match s.spine with
             | some (s_h, s_sp) =>  do
                    let ps' : Vect n (Option (List SpineElem × Term)) := (λ x => do
                      let (p_h, p_sp) <- x.fst.spine
                      if (p_h == s_h) then return (p_sp, x.snd) else none) <$> ps.zip cs
                    match ps'.any with
                    | some (sp', t) =>
                      match prefix_equal sp' s_sp with
                      | some p => t.apply p
                      | none => none -- stuck
                    | none => return default
             | none => none

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
match eval_const_folding_refl G t with
             | .some t => .some t
             | .none => eval_inst_beta G t

end Core
