
import SystemFD.Term

import SystemFD.Examples.Apoorv

instance : Monad List where -- This seems fishy. Why doesn't lean have a Monad List instance?
  pure a := List.cons a List.nil
  bind l f := List.flatMap l f


def optionToListList {A : Type} : Option A -> List (List A)
  | .none => [[]]
  | .some x => [[x]]


def optionToList {A : Type} : Option A -> List A
  | .none => []
  | .some x => [x]


def eval_ctx (ctx : Ctx Term) : List Term -> List Term
  | .cons #x tl => (match (ctx d@ x) with
                   | .term _ t => .cons t tl
                   | _ => #x :: tl)

  | .cons (.ctor2 .app (.bind2 .lam _ b) t) tl => b β[ t ] :: tl
  | .cons (.ctor2 .app f t) tl => do
    let f' <- eval_ctx ctx [ f ]
    (f' `@ t) :: tl -- call by name

  | .cons (.ctor2 .appt (.bind2 .lamt _ b) ty) tl => b β[ ty ] :: tl
  | .cons (.ctor2 .appt f t) tl => do
    let f' <- eval_ctx ctx [ f ]
    (f' `@t t) :: tl -- call by name

  -- | .cons (.ite (.var x) (.var y) b c) tl => -- TODO: Get the head and the args to build a substitution
  --   (if x == y then b else c) :: tl

  | .cons (.ite p s b c) tl => do
  let h <- optionToList (Term.neutral_head p)
  (match Term.neutral_form s with
  | .none => do let s'' <- eval_ctx ctx [ s ]
                .ite p s'' b c :: tl
  | .some (s' , l) => (if (h == s')
                      then Term.apply_spine b l :: tl
                      else c :: tl))

  --------------------------
  ---- Coercions
  --------------------------
  | .cons (.ctor1 .sym (.ctor1 .refl ty)) tl => refl! ty :: tl
  | .cons (.ctor2 .cast t (.ctor1 .sym (.ctor2 .seq η η'))) tl =>
    (t ▹ (sym! η' `; sym! η)) :: tl
  | .cons (.ctor2 .seq (.ctor1 .refl ty') (.ctor1 .refl ty)) tl =>
    if ty == ty'
    then refl! ty :: tl
    else (.ctor2 .seq (.ctor1 .refl ty') (.ctor1 .refl ty)) :: tl -- stuck
  | .cons (.ctor2 .appc (.ctor1 .refl (.ctor2 .arrow ty ty')) (.ctor1 .refl ty'')) tl =>
    if ty == ty''
    then refl! ty' :: tl
    else (.ctor2 .appc (.ctor1 .refl (.ctor2 .arrow ty ty')) (.ctor1 .refl ty'')) :: tl -- stuck
  | .cons (.ctor1 .refl (.ctor1 .fst (.ctor1 .refl (.ctor2 .app A B)))) tl =>
     refl! A :: tl
  | .cons (.ctor1 .refl (.ctor1 .snd (.ctor1 .refl (.ctor2 .app A B)))) tl =>
     refl! B :: tl
  | .cons (.ctor2 .arrowc (.ctor1 .refl ty) (.ctor1 .refl ty')) tl => .ctor1 .refl (ty -t> ty') :: tl
  | .cons (.bind2 .allc ty (.ctor1 .refl ty')) tl => .ctor1 .refl (∀[ty] ty') :: tl
  | .cons (.ctor2 .cast t (.ctor1 .refl _)) tl => t :: tl
  | .cons (.ctor2 .cast t η) tl => do
    let η' <- eval_ctx ctx [ η ]
    (t ▹ η') :: tl


  -- | .cons (.inst n t t) tl =>
  ---------------
  ----Decls
  ---------------
  | .cons (.letdata K t) tl => eval_ctx (.datatype K :: ctx) (t :: tl)
  | .cons (Term.letterm ty t t') tl => eval_ctx (.term ty t :: ctx) (t' :: tl)
  | .cons (.bind2 .letctor t t') tl => eval_ctx (.ctor t :: ctx) (t' :: tl)
  | .cons (.bind2 .letopentype t t') tl => eval_ctx (.opent t :: ctx) (t' :: tl)
  | .cons (.bind2 .letopen t t') tl => eval_ctx (.openm t :: ctx) (t' :: tl)
  | .cons (.bind2 .insttype t t') tl => eval_ctx (.insttype t :: ctx) (t' :: tl)

  | t => t
  decreasing_by
    repeat sorry

def mkCtx (ctx : Ctx Term) : Term -> Ctx Term
  | .letdata K t => mkCtx (.datatype K :: ctx ) t
  | .letterm ty t t' => mkCtx (.term ty t ::  ctx) t'
  | .bind2 .letctor t t' => mkCtx (.ctor t :: ctx) t'
  | .bind2 .letopentype t t' => mkCtx (.opent t :: ctx) t'
  | .bind2 .letopen t t' => mkCtx (.openm t :: ctx) t'
  | .bind2 .insttype t t' => mkCtx (.insttype t :: ctx) t'
  | .inst n t t' => mkCtx (.inst n t :: ctx) t'
  | _ => ctx

unsafe def eval_ctx_loop (ctx : Ctx Term) (t : List Term) : List Term :=
  let t' := eval_ctx ctx t
  if t == t'
  then t'
  else eval_ctx_loop ctx t'

unsafe def eval (t : Term) : List Term :=
  let ctx := mkCtx [] t;
  eval_ctx_loop ctx [t]

#eval infer_type (mkCtx [] unit) unit
#eval! eval unit

#eval infer_type (mkCtx [] unitRefl) unitRefl
#eval! eval unitRefl


#eval! eval booltest2
