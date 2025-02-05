
import SystemFD.Util
import SystemFD.Term
import SystemFD.Algorithm

instance : Monad List where -- This seems fishy. Why doesn't lean have a Monad List instance?
  pure a := List.cons a List.nil
  bind l f := List.flatMap l f

def optionToList {A : Type} : Option A -> List A
  | .none => []
  | .some x => [x]

-- Evaluation for a term in a context
def eval_ctx (ctx : Ctx Term) : Term -> List Term
  -- | #x => match (ctx d@ x) with
  --                  | .term _ t => [t]
  --                  | _ => [#x]

  | .ctor2 .app (.bind2 .lam _ b) t
  | .ctor2 .appt (.bind2 .lamt _ b) t => [b β[ t ]]

  | .ctor2 .app f t => do
    let f' <- eval_ctx ctx f
    [f' `@ t] -- call by name

  | .ctor2 .appt f t => do
    let f' <- eval_ctx ctx f
    [f' `@t t] -- call by name

  --------------------------
  ---- Case matching
  --------------------------
  | .ite p s b c => do
    let (h, sp) <- optionToList (Term.neutral_form p)
    (match Term.neutral_form s with
    | .none => do let s'' <- eval_ctx ctx s
                  [.ite p s'' b c]
    | .some (s' , sp') => (if (h == s')
                          then match prefix_equal sp sp' with
                               | .some l => [Term.apply_spine b l]
                               | .none => [c]
                          else [c]))

  --------------------------
  ---- Guards over open terms
  --------------------------
  | .guard p s c => do
    let (p', sp) <- optionToList (Term.neutral_form p)
    (match Term.neutral_form s with
    | .none => do let s'' <- eval_ctx ctx s
                  [.guard p s'' c]
    | .some (s' , sp') => (if (p' == s')
                          then match prefix_equal sp sp' with
                               | .some l =>  [Term.apply_spine c l]
                               | .none   => []
                          else []))

  --------------------------
  ---- Coercions
  --------------------------
  | .ctor1 .sym (.ctor1 .refl ty) => [refl! ty]
  | .ctor2 .cast t (.ctor1 .sym (.ctor2 .seq η η')) => [t ▹ (sym! η' `; sym! η)]
  | .ctor2 .seq (.ctor1 .refl ty') (.ctor1 .refl ty) =>
    if ty == ty'
    then [refl! ty]
    else [.ctor2 .seq (.ctor1 .refl ty') (.ctor1 .refl ty)] -- stuck
  | .ctor2 .appc (.ctor1 .refl (.bind2 .arrow ty ty')) (.ctor1 .refl ty'') =>
    if ty == ty''
    then [refl! ty']
    else [.ctor2 .appc (.ctor1 .refl (.bind2 .arrow ty ty')) (.ctor1 .refl ty'')] -- stuck
  | .ctor1 .refl (.ctor1 .fst (.ctor1 .refl (.ctor2 .app A _))) =>
     [refl! A]
  | .ctor1 .refl (.ctor1 .snd (.ctor1 .refl (.ctor2 .app _ B))) =>
     [refl! B]
  | .ctor2 .arrowc (.ctor1 .refl ty) (.ctor1 .refl ty') => [.ctor1 .refl (ty -t> ty')]
  | .bind2 .allc ty (.ctor1 .refl ty') => [.ctor1 .refl (∀[ty] ty')]
  | .ctor2 .cast t (.ctor1 .refl _) => [t]
  | .ctor2 .cast t η => do
    let η' <- eval_ctx ctx η
    [t ▹ η']


  ---------------
  ----Decls
  ---------------
  | .letdata K t => eval_ctx (.datatype K :: ctx) t
  | Term.letterm ty t t' => eval_ctx (.term ty t :: ctx) t'
  | .bind2 .letctor t t' => eval_ctx (.ctor t :: ctx) t'
  | .bind2 .letopentype t t' => eval_ctx (.opent t :: ctx) t'
  | .bind2 .letopen t t' => eval_ctx (.openm t :: ctx) t'
  | .bind2 .insttype t t' => eval_ctx (.insttype t :: ctx) t'

  | t => [t]


-- Instantiates instances or performs a one step evaluation
def eval_inst (Γ : Ctx Term) (t : Term) : List Term :=
  match (Term.neutral_form t) with
  | .none => eval_ctx Γ t
  | .some (h, sp) =>
    match (Γ @ h) with
    | .openm _ => let ιs := instance_indices' Γ 0 h [] ; -- get all the indices of instances
         let ts := get_instances Γ ιs ; -- select the right instances using the indices
         List.map (λ x => x.apply_spine sp) ts -- apply the instance terms to the spine
    | .term _ b => [b.apply_spine sp]
    | _ => [t]


-- Goes over the list of terms and evaluates each of them by one step
def eval_outer (Γ : Ctx Term) (ts : List Term) : List Term := List.flatMap ts (eval_inst Γ)

-- multistep evaluator
unsafe def eval_ctx_loop (Γ : Ctx Term) (t : Term) : List Term := do
  let t' <- eval_outer Γ [t]
  if t == t'
  then [t']
  else eval_ctx_loop Γ t'

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
