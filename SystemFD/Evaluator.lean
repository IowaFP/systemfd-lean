import SystemFD.Examples

#eval "Hello world!"

instance : Monad List where -- This seems fishy. Why doesn't lean have a Monad List instance?
  pure a := List.cons a List.nil
  bind l f :=
    match l with
    | List.nil => .nil
    | List.cons x xs => f x ++ List.flatMap xs f


def eval_ctx (ctx : Ctx Term) : List Term -> List Term
  | .cons #x tl => match (dnth ctx x) with
          | .term _ t => .cons t tl
          | _ => #x :: eval_ctx ctx tl

  | .cons (.ctor2 .app (.bind2 .lam _ b) t) tl => b β[ t ] :: tl
  | .cons (.ctor2 .app f t) tl => do
    let f' <- eval_ctx ctx [ f ]
    (f' `@ t) :: tl -- call by name

  | .cons (.ctor2 .appt (.bind2 .lamt _ b) ty) tl => b β[ ty ] :: tl
  | .cons (.ctor2 .appt f t) tl => do
    let f' <- eval_ctx ctx [ f ]
    (f' `@t t) :: tl -- call by name

  | .cons (.ite (.var x) (.var y) b c) tl =>
    (if x == y then b else c) :: tl

  | .cons (.ite p s b c) tl => do
  let s' <- eval_ctx ctx [ s ]
  (.ite p s' b c) :: tl

  | .cons (.ctor2 .cast t (.ctor1 .refl _)) tl => t :: tl
  | .cons (.ctor2 .cast t η) tl => do
    let η' <- eval_ctx ctx [ η ]
    (t ▹ η') :: tl

  /-  | .cons (.ctor2 .cast t (.ctor1 .sym (.ctor2 .seq η η'))) tl =>
    (t ▹ (eval_ctx ctx (sym η') `; eval_ctx ctx (sym η))) :: tl
  -/
  | .cons (.letdata K n t) tl => eval_ctx (.datatype K n :: ctx) (t :: tl)

  | .cons (Term.letterm ty t t') tl => eval_ctx (.term ty t :: ctx) (t' :: tl)

  | .cons (.bind2 .letctor t t') tl => eval_ctx (.ctor t :: ctx) (t' :: tl)

  | .cons (.bind2 .letopentype t t') tl => eval_ctx (.opent t :: ctx) (t' :: tl)

  | .cons (.bind2 .letopen t t') tl => eval_ctx (.openm t :: ctx) (t' :: tl)

  | .cons (.bind2 .insttype t t') tl => eval_ctx (.insttype t :: ctx) (t' :: tl)

  | t => t

def eval (t : Term) : List Term := eval_ctx [] [t]

def mkCtx (ctx : Ctx Term) : Term -> Ctx Term
  | .letdata K n t => mkCtx (.datatype K n :: ctx ) t
  | .letterm ty t t' => mkCtx (.term ty t ::  ctx) t'
  | .bind2 .letctor t t' => mkCtx (.ctor t :: ctx) t'
  | .bind2 .letopentype t t' => mkCtx (.opent t :: ctx) t'
  | .bind2 .letopen t t' => mkCtx (.openm t :: ctx) t'
  | .bind2 .insttype t t' => mkCtx (.insttype t :: ctx) t'
  | _ => ctx

#eval! eval unitRefl
#eval! eval unitType
#eval! let ctx := mkCtx [] booltest ; eval_ctx ctx (eval_ctx ctx (eval_ctx ctx [booltest]))
