
import SystemFD.Util
import SystemFD.Term

set_option maxHeartbeats 500000


-- Instantiates instances/performs a one step term evaluation
@[simp]
def eval_inst (Γ : Ctx Term) (t : Term) : Option Term :=
  match t with -- we need to evaulate a non-variable term
    | .var h =>
      match (Γ d@ h) with
      | .openm _ => do
        let ιs := get_instances Γ h -- select the right instances using the indices
        .some (List.foldl (·⊕·) `0 ιs)
      | .term _ b => b  -- inline a let bound term
      | _ => .none -- do not evaluate

    | .ctor2 .app (.bind2 .lam _ b) t => .some (b β[ t ])
    | .ctor2 .appt (.bind2 .lamt _ b) t => .some (b β[ t ])
    | Term.letterm _ t t' => .some (t' β[ t ])

    | .ctor2 .app f t => do
      match f.neutral_form with
      | .some (h, sp) =>
        (match (Γ d@ h) with
          | .openm _ => do
            let ιs := get_instances Γ h ; -- get all instances
            let ts := List.map (·.apply_spine sp) ιs -- apply the instance terms to the spine
            -- let ts' := List.map (· `@ t) ts
            .some (List.foldl (·⊕·) `0 ts `@ t)
          | .term _ b => .some ((b.apply_spine sp) `@ t)  -- inline a let bound term
          | _ => .none ) -- nothing to evaluate to
      | .none => do
          let f' <- eval_inst Γ f
          .some (f' `@ t) -- call by name

    | .ctor2 .appt f t => do
      match f.neutral_form with
      | .some (h, sp) =>
        (match (Γ d@ h) with
          | .openm _ =>
            let ιs := get_instances Γ h ; -- get all instances
            let ts := List.map (·.apply_spine sp) ιs -- apply the instance terms to the spine
            -- let ts' := List.map (· `@ t) ts
            .some (List.foldl (·⊕·) `0 ts `@t t)
          | .term _ b => .some (b.apply_spine sp `@t t)  -- inline a let bound term
          | _ => .none) -- do not evaluate
      | .none => do
          let f' <- eval_inst Γ f
          .some (f' `@t t) -- call by name

  --------------------------
  ---- Case matching
  --------------------------
    | .ite p s b c => do
      let (h, sp) <- Term.neutral_form p
      if Γ.is_ctor h
      then (match Term.neutral_form s with
            | .none => do let s'' <- eval_inst Γ s
                          .some (.ite p s'' b c)
            | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
              if ¬ (Γ.is_stable_red s')
              then do let s'' <- eval_inst Γ s
                      .some (.ite p s'' b c)
              else ( -- s' cannot be a term or an instance
                     -- if it is then evaluate by eval_inst
                     if h == s'
                     then match (prefix_equal sp sp') with
                          | .some l => .some (Term.apply_spine b l)
                          | _ => .some c
                     else .some c
                     ))
      else .none

  --------------------------
  ---- Guards over open terms
  --------------------------
    | .guard p s c => do
      let (p', sp) <- Term.neutral_form p
      if Γ.is_insttype p'
      then match Term.neutral_form s with
           | .none => do
             let s'' <- eval_inst Γ s
             .some (.guard p s'' c)
           | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
             if ¬ (Γ.is_stable_red s')
             then do
               let s'' <- eval_inst Γ s
               .some (.guard p s'' c)
             else
                if p' == s'
                then match prefix_equal sp sp' with
                     | .some l => .some (c.apply_spine l)
                     | _                 => .some `0 -- guards failing return empty list
                else .some `0
      else .none

  --------------------------
  ---- Coercions
  --------------------------
    | .ctor1 .sym (.ctor2 .refl K t) => refl! K t
    | .ctor1 .sym η => do
      let η' <- eval_inst Γ η
      .some (sym! η')

    | .ctor2 .seq (.ctor2 .refl K t) (.ctor2 .refl K' t') =>
      if t == t' && K == K' -- matched during type checking?
      then .some (refl! K t)
      else .none
    | .ctor2 .seq (.ctor2 .refl K t) η2 => do
      let η2' <- eval_inst Γ η2
      .some (refl! K t `; η2')
    | .ctor2 .seq η1 η2 => do
      let η1' <- eval_inst Γ η1
      .some (η1' `; η2)

    | .ctor2 .appc (.ctor2 .refl (K1 -k> K) t) (.ctor2 .refl K2 t') =>
      if K1 == K2  -- ideally argument kinds match, but thats done by type checker
      then .some (refl! K (t `@k t'))
      else .none
    | .ctor2 .appc (.ctor2 .refl K t) η2 => do
      let η2' <- eval_inst Γ η2
      .some ((.ctor2 .refl K t) `@c η2')
    | .ctor2 .appc η1 η2 => do
      let η1' <- eval_inst Γ η1
      .some (η1' `@c η2)

    | .ctor2 .fst K1 (.ctor2 .refl K2 (.ctor2 .appk A _)) =>
      .some (refl! (K1 -k> K2) A)
    | .ctor2 .fst K η => do
       let η' <- eval_inst Γ η
       .some (fst! K η')

    | .ctor2 .snd K1 (.ctor2 .refl _ (.ctor2 .appk _ B)) =>
      .some (refl! K1 B)
    | .ctor2 .snd K1 η => do
       let η' <- eval_inst Γ η
       .some (snd! K1 η')

    | .bind2 .arrowc (.ctor2 .refl ★ t) (.ctor2 .refl ★ t') => .some (refl! ★ (t -t> t'))
    | .bind2 .arrowc (.ctor2 .refl ★ t) η => do
      let η' <- eval_inst (.empty :: Γ) η
      .some ((refl! ★ t) -c> η')
    | .bind2 .arrowc η η' => do
      let η'' <- eval_inst Γ η
      .some (η'' -c> η')

    | .bind2 .allc t (.ctor2 .refl K t') => .some (refl! K (∀[t] t'))
    | .bind2 .allc t η => do
      let η' <- eval_inst (.kind t :: Γ) η
      .some (∀c[t] η')

    | .ctor2 .apptc (.ctor2 .refl K1 (.bind2 .all K2 t1)) (.ctor2 .refl K2' t2) =>
      if K2 == K2'
      then .some (refl! K1 (t1 β[t2]))
      else .none
    | .ctor2 .apptc η1 (.ctor2 .refl K t) => do
      let η1' <- eval_inst Γ η1
      .some (η1' `@c[refl! K t])
    | .ctor2 .apptc η1 η2 => do
      let η2' <- eval_inst Γ η2
      .some (η1 `@c[ η2' ])

    | .ctor2 .cast t (.ctor2 .refl _ _) => .some t
    | .ctor2 .cast t η => do
      let η' <- eval_inst Γ η
      .some (t ▹ η')

    | `0 => .none

    | .ctor2 .choice `0 t2 => t2
    | .ctor2 .choice t1 `0 => t1
    | .ctor2 .choice t1 t2 => do -- for now, go left to right on choice, get stuck if left choice evals to non-zero
      let t1' <- eval_inst Γ t1
      .some (.ctor2 .choice t1' t2)

    | _ => .none


-- Goes over the list of terms and evaluates each of them by one step
-- @[simp]
-- def eval_outer (Γ : Ctx Term) (ts : Term) : Option Term :=
--   match ts with
--   | `0 => .some `0
--   | .choice t ts => do
--     let t' <- eval_inst Γ t
--     let ts' <- eval_outer Γ ts
--     .some (t' ++ ts')

-- multistep evaluator
unsafe def eval_ctx_loop (Γ : Ctx Term) (t : Term) : Term :=
  match (eval_inst Γ t) with
  | .none => t
  | .some t => eval_ctx_loop Γ t

unsafe def eval (t : Term) : Term := eval_ctx_loop [] t
