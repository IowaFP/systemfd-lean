
import SystemFD.Util
import SystemFD.Term

set_option maxHeartbeats 500000


-- Instantiates instances/performs a one step term evaluation
@[simp]
def eval_inst (Γ : Ctx Term) (t : Term) : Option (List Term) :=
  match t with -- we need to evaulate a non-variable term
    | .var h =>
      match (Γ d@ h) with
      | .openm _ =>
            let ιs := instance_indices Γ 0 h [] ; -- get all the indices of instances
            get_instances Γ ιs -- select the right instances using the indices
          | .term _ b => [ b ]  -- inline a let bound term
          | _ => .none -- do not evaluate

    | .ctor2 .app (.bind2 .lam _ b) t
    | .ctor2 .appt (.bind2 .lamt _ b) t => .some [b β[ t ]]
    | Term.letterm _ t t' => .some [t' β[ t ]]

    | .ctor2 .app f t => do
      match f.neutral_form with
      | .some (h, sp) =>
        (match (Γ d@ h) with
          | .openm _ =>
            let ιs := instance_indices Γ 0 h [] ; -- get all the indices of instances
            let ts := get_instances Γ ιs ; -- select the right instances using the indices
            let ts' := List.map (·.apply_spine sp) ts -- apply the instance terms to the spine
            List.map (· `@ t) ts'
          | .term _ b => [ b.apply_spine sp `@ t]  -- inline a let bound term
          | _ => .none) -- do not evaluate
      | .none => do
          let f' <- eval_inst Γ f
          .some (List.map (· `@ t) f') -- call by name

    | .ctor2 .appt f t => do
      match f.neutral_form with
      | .some (h, sp) =>
        (match (Γ d@ h) with
          | .openm _ =>
            let ιs := instance_indices Γ 0 h [] ; -- get all the indices of instances
            let ts := get_instances Γ ιs ; -- select the right instances using the indices
            let ts' := List.map (·.apply_spine sp) ts -- apply the instance terms to the spine
            List.map (· `@t t) ts'
          | .term _ b => [ b.apply_spine sp `@t t]  -- inline a let bound term
          | _ => .none) -- do not evaluate
      | .none => do
          let f' <- eval_inst Γ f
          .some (List.map (· `@t t) f') -- call by name

  --------------------------
  ---- Case matching
  --------------------------
    | .ite p s b c => do
      let (h, sp) <- Term.neutral_form p
      if Γ.is_ctor h
      then (match Term.neutral_form s with
            | .none => do let s'' <- eval_inst Γ s
                          .some (List.map (.ite p · b c) s'')
            | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
              if ¬ (Γ.is_stable_red s')
              then do let s'' <- eval_inst Γ s
                      .some (List.map (.ite p · b c) s'')
              else ( -- s' cannot be a term or an instance
                     -- if it is then evaluate by eval_inst
                     if h == s'
                          then match (prefix_equal sp sp') with
                               | .some l => .some [Term.apply_spine b l]
                               | _ => .some [c]
                          else .some [c]
                     ))
      else .none

  --------------------------
  ---- Guards over open terms
  --------------------------
    | .guard p s c => do
      let (p', sp) <- Term.neutral_form p
      if Γ.is_insttype p'
      then (match Term.neutral_form s with
           | .none => do let s'' <- eval_inst Γ s
                         .some (List.map (.guard p · c) s'')
           | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
             if ¬ (Γ.is_stable_red s')
             then do let s'' <- eval_inst Γ s
                     .some (List.map (.guard p · c) s'')
             else (if (p' == s')
                  then (match prefix_equal sp sp' with
                       | .some l => .some [c.apply_spine l]
                       | _                 => .some []) -- guards failing return empty list
                  else .some []))
      else .none

  --------------------------
  ---- Coercions
  --------------------------
    | .ctor1 .sym (.ctor1 .refl t) => [refl! t]
    | .ctor1 .sym η => do
      let η' <- eval_inst Γ η
      .some (List.map (sym! ·) η')
    | .ctor2 .seq (.ctor1 .refl t') (.ctor1 .refl t) =>
      if t == t'
      then .some [refl! t]
      else .none

    | .ctor2 .appc (.ctor1 .refl t) (.ctor1 .refl t') =>
      .some [refl! (t `@k t')]
    | .ctor1 .fst (.ctor1 .refl (.ctor2 .appk A _)) =>
      .some [refl! A]
    | .ctor1 .snd (.ctor1 .refl (.ctor2 .appk _ B)) =>
      .some [refl! B]

    | .bind2 .arrowc (.ctor1 .refl t) (.ctor1 .refl t') => .some [refl! (t -t> t')]
    | .bind2 .arrowc (.ctor1 .refl t) η => do
      let η' <- eval_inst (.empty :: Γ) η
      .some (List.map (refl! t -c> ·) η')
    | .bind2 .arrowc η η' => do
      let η'' <- eval_inst Γ η
      .some (List.map (· -c> η') η'')
    | .bind2 .allc t (.ctor1 .refl t') => .some [refl! (∀[t] t')]
    | .bind2 .allc t η => do
      let η' <- eval_inst (.kind t :: Γ) η
      .some (List.map (∀c[t] ·) η')
    | .ctor2 .cast t (.ctor1 .refl _) => .some [t]
    | .ctor2 .cast t η => do
      let η' <- eval_inst Γ η
      .some (List.map (t ▹ ·) η')

    | _ => .none


-- Goes over the list of terms and evaluates each of them by one step
@[simp]
def eval_outer (Γ : Ctx Term) (ts : List Term) : Option (List Term) :=
  match ts with
  | [] => .some []
  | .cons t ts => do
    let t' <- eval_inst Γ t
    let ts' <- eval_outer Γ ts
    .some (t' ++ ts')

-- multistep evaluator
unsafe def eval_ctx_loop (Γ : Ctx Term) (t : Term) : List Term := do
  match (eval_outer Γ [t]) with
  | .none => [t]
  | .some ts => List.flatMap ts (eval_ctx_loop Γ)

unsafe def eval (t : Term) : List Term :=
  eval_ctx_loop [] t
