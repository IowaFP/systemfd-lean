
import SystemFD.Util
import SystemFD.Term
import SystemFD.Algorithm
set_option maxHeartbeats 500000


-- Instantiates instances/performs a one step term evaluation
@[simp]
def eval_inst (Γ : Ctx Term) (t : Term) : Option (List Term) :=
  match Term.neutral_form t with
  | .some (h, sp) =>
    match (Γ d@ h) with
    | .openm _ => let ιs := instance_indices' Γ 0 h [] ; -- get all the indices of instances
         let ts := get_instances Γ ιs ; -- select the right instances using the indices
         List.map (·.apply_spine sp) ts -- apply the instance terms to the spine

    | .term _ b => .some [ b.apply_spine sp ]  -- inline a let bound term
    | _ => .none -- do not evaluate
  | .none => match t with -- we need to evaulate a non-variable term
    | .ctor2 .app (.bind2 .lam _ b) t
    | .ctor2 .appt (.bind2 .lamt _ b) t => .some [b β[ t ]]

    | .ctor2 .app f t => do
      let f' <- eval_inst Γ f
      .some (List.map (· `@ t) f') -- call by name

    | .ctor2 .appt f t => do
      let f' <- eval_inst Γ f
      .some (List.map (· `@t t) f') -- call by name

  --------------------------
  ---- Case matching
  --------------------------
    | .ite p s b c => do
      let (h, sp) <- Term.neutral_form p
      (match Term.neutral_form s with
      | .none => do let s'' <- eval_inst Γ s
                    .some (List.map (.ite p · b c) s'')
      | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
              if Term.is_letterm Γ s' || Term.is_openmethod Γ s'
              then do let s'' <- eval_inst Γ s
                      .some (List.map (.ite p · b c) s'')
              else ( -- s' cannot be a term or an instance
                     -- if it is then evaluate by eval_inst
                     match (h == s' , prefix_equal sp sp') with
                         | (.true , .some l) => .some [Term.apply_spine b l]
                         | _ => .some [c]))

  --------------------------
  ---- Guards over open terms
  --------------------------
    | .guard p s c => do
      let (p', sp) <- Term.neutral_form p
      (match Term.neutral_form s with
       | .none => do let s'' <- eval_inst Γ s
                     .some (List.map (.guard p · c) s'')
       | .some (s' , sp') =>
              -- s can be neutral, but the head is a let term or an open method
              -- so instantiate it
          if Term.is_letterm Γ s' || Term.is_openmethod Γ s'
          then do let s'' <- eval_inst Γ s
                  .some (List.map (.guard p · c) s'')
          else match (p' == s', prefix_equal sp sp') with
                          | (.true , .some l) => .some [c.apply_spine l]
                          | _                 => .some []) -- guards failing return empty list

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

    | .ctor2 .appc (.ctor1 .refl (.bind2 .arrow t t')) (.ctor1 .refl t'') =>
      if t == t''
      then .some [refl! t']
      else .none
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


  ---------------
  ----Decls
  ---------------
    | .letdata K t => do
      let t' <- eval_inst (.datatype K :: Γ) t
      .some (List.map (.letdata K ·) t')
    | Term.letterm ty t t' => do
      let t'' <- eval_inst (.term ty t :: Γ) t'
      .some (List.map (.letterm ty t ·) t'')
    | .bind2 .letctor t t' => do
      let t'' <- eval_inst (.ctor t :: Γ) t'
      .some (List.map (letctor! t ·) t'')
    | .bind2 .letopentype t t' => do
      let t'' <- eval_inst (.opent t :: Γ) t'
      .some (List.map (letopentype! t ·) t'')
    | .bind2 .letopen t t' => do
      let t'' <- eval_inst (.openm t :: Γ) t'
      .some (List.map (letopen! t ·) t'')
    | .bind2 .insttype t t' => do
      let t'' <- eval_inst (.insttype t :: Γ) t'
      .some (List.map (insttype! t ·) t'')

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

@[simp]
def mkCtx (ctx : Ctx Term) : Term -> Ctx Term
  | .letdata K t => mkCtx (.datatype K :: ctx ) t
  | .letterm ty t t' => mkCtx (.term ty t ::  ctx) t'
  | .bind2 .letctor t t' => mkCtx (.ctor t :: ctx) t'
  | .bind2 .letopentype t t' => mkCtx (.opent t :: ctx) t'
  | .bind2 .letopen t t' => mkCtx (.openm t :: ctx) t'
  | .bind2 .insttype t t' => mkCtx (.insttype t :: ctx) t'
  | .inst n t t' => mkCtx (.inst n t :: ctx) t'
  | _ => ctx

unsafe def eval (t : Term) : List Term :=
  let ctx := mkCtx [] t;
  eval_ctx_loop ctx t
