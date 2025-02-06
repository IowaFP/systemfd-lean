
import SystemFD.Util
import SystemFD.Term
import SystemFD.Algorithm

instance : Monad List where -- This seems fishy. Why doesn't lean have a Monad List instance?
  pure a := List.cons a List.nil
  bind l f := List.flatMap l f

-- Evaluation for a term in a context
def eval_ctx (ctx : Ctx Term) : Term -> Option (List Term)  -- | #x => match (ctx d@ x) with

  | .ctor2 .app (.bind2 .lam _ b) t
  | .ctor2 .appt (.bind2 .lamt _ b) t => .some [b β[ t ]]

  | .ctor2 .app f t => do
    let f' <- eval_ctx ctx f
    .some (List.map (λ x => x `@ t) f') -- call by name

  | .ctor2 .appt f t => do
    let f' <- eval_ctx ctx f
    .some (List.map (· `@ t) f') -- call by name

  --------------------------
  ---- Case matching
  --------------------------
  | .ite p s b c => do
    let (h, sp) <- Term.neutral_form p
    (match Term.neutral_form s with
    | .none => do let s'' <- eval_ctx ctx s
                  .some (List.map (.ite p · b c) s'')
    | .some (s' , sp') => (if (h == s')
                          then match prefix_equal sp sp' with
                               | .some l => .some [Term.apply_spine b l]
                               | .none => .some [c]
                          else .some [c]))

  --------------------------
  ---- Guards over open terms
  --------------------------
  | .guard p s c => do
    let (p', sp) <- Term.neutral_form p
    (match Term.neutral_form s with
    | .none => do let s'' <- eval_ctx ctx s
                  .some (List.map (.guard p · c) s'')
    | .some (s' , sp') => match (p' == s', prefix_equal sp sp') with
                          | (.true , .some l) => .some [c.apply_spine l]
                          | _                 => .some []) -- guards failing return empty list

  --------------------------
  ---- Coercions
  --------------------------
  | .ctor1 .sym (.ctor1 .refl t) => [refl! t]
  | .ctor1 .sym η => do
    let η' <- eval_ctx ctx η
    .some (List.map (sym! ·) η')
  | .ctor2 .seq (.ctor1 .refl t') (.ctor1 .refl t) =>
    if t == t'
    then .some [refl! t]
    else .none

  | .ctor2 .appc (.ctor1 .refl (.bind2 .arrow t t')) (.ctor1 .refl t'') =>
    if t == t''
    then .some [refl! t']
    else .none
  | .ctor1 .refl (.ctor1 .fst (.ctor1 .refl (.ctor2 .app A _))) =>
     .some [refl! A]
  | .ctor1 .refl (.ctor1 .snd (.ctor1 .refl (.ctor2 .app _ B))) =>
     .some [refl! B]

  | .bind2 .arrowc (.ctor1 .refl t) (.ctor1 .refl t') => .some [refl! (t -t> t')]
  | .bind2 .arrowc (.ctor1 .refl t) η => do
    let η' <- eval_ctx (.empty :: ctx) η
    .some (List.map (refl! t -c> ·) η')
  | .bind2 .arrowc η η' => do
    let η'' <- eval_ctx ctx η
    .some (List.map (· -c> η') η'')
  | .bind2 .allc t (.ctor1 .refl t') => .some [refl! (∀[t] t')]
  | .bind2 .allc t η => do
    let η' <- eval_ctx (.kind t :: ctx) η
    .some (List.map (∀c[t] ·) η')
  | .ctor2 .cast t (.ctor1 .refl _) => .some [t]
  | .ctor2 .cast t η => do
    let η' <- eval_ctx ctx η
    .some (List.map (t ▹ ·) η')


  ---------------
  ----Decls
  ---------------
  | .letdata K t => do
    let t' <- eval_ctx (.datatype K :: ctx) t
    .some (List.map (.letdata K ·) t')
  | Term.letterm ty t t' => do
    let t'' <- eval_ctx (.term ty t :: ctx) t'
    .some (List.map (.letterm ty t ·) t'')
  | .bind2 .letctor t t' => do
    let t'' <- eval_ctx (.ctor t :: ctx) t'
    .some (List.map (letctor! t ·) t'')
  | .bind2 .letopentype t t' => do
    let t'' <- eval_ctx (.opent t :: ctx) t'
    .some (List.map (letopentype! t ·) t'')
  | .bind2 .letopen t t' => do
    let t'' <- eval_ctx (.openm t :: ctx) t'
    .some (List.map (letopen! t ·) t'')
  | .bind2 .insttype t t' => do
    let t'' <- eval_ctx (.insttype t :: ctx) t'
    .some (List.map (insttype! t ·) t'')

  | _ => .none


-- Instantiates instances/performs a one step term evaluation
def eval_inst (Γ : Ctx Term) (t : Term) : Option (List Term) :=
  match Term.neutral_form t with
  | .some (h, sp) =>
    match (Γ d@ h) with
    | .openm _ => let ιs := instance_indices' Γ 0 h [] ; -- get all the indices of instances
         let ts := get_instances' Γ ιs ; -- select the right instances using the indices
         List.map (λ x => x.apply_spine sp) ts -- apply the instance terms to the spine

    | .term _ b => .some [ b.apply_spine sp ]  -- inline a let bound term (after shifting)
    | _ => .none -- do not evaluate
  | .none => eval_ctx Γ t


-- Goes over the list of terms and evaluates each of them by one step
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
