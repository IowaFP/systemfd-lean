import SystemFD.Examples

#eval "Hello world!"

def eval_ctx (ctx : Ctx Term) : List Term -> List Term
  | (.cons #x tl) => match (dnth ctx x) with
          | .term _ t => .cons t tl
          | _ => #x :: eval_ctx ctx tl
  | (.cons (.ctor2 .app (.bind2 .lam _ b) t) tl) => b β[ t ] :: tl
  -- | (.cons (.ctor2 .app f t) tl) => do tl
    -- let .cons f' .nil <- eval_ctx ctx [ f ]
    -- tl-- call by name

/-  | (Λ[ _ ] x) `@t ty => x β[ ty ]
  | f `@t ty => eval_ctx ctx f `@t ty

  | t ▹ (.refl _) => t
  | t ▹ η => t ▹ (eval_ctx ctx η)
  /-  | t ▹ .sym (η `; η') => t ▹ (eval_ctx ctx (sym η') `; eval_ctx ctx (sym η)) -/

  | Term.letdata K n t => eval_ctx (List.cons (.datatype K n) ctx) t
  | Term.letctor t t' => eval_ctx (List.cons (.ctor t) ctx) t'

  | Term.letopentype k t => eval_ctx (List.cons (.opent k) ctx) t
  | Term.letopen ty t => eval_ctx (List.cons (.insttype ty) ctx) t

  | Term.letterm _ t t' => eval_ctx (List.cons (.term t) ctx) t'

  | Term.insttype ty t' => eval_ctx (List.cons (.opent ty) ctx) t'
 -/
  | .cons t tl => t :: tl
  | [] => []

def eval (t : Term) : List Term := eval_ctx [.empty] [t]

#eval eval unitRefl
#eval eval unitType
#eval eval booltest
