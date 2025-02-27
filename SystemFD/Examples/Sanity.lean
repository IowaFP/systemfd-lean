
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def boolCtx : Ctx Term := [
    .ctor #1 -- True : Bool
  , .ctor #0 -- False : Bool
  , .datatype  ★   -- Bool : ★
]
#eval wf_ctx boolCtx

def test : Ctx Term := [

    .datatype ★
  -- Just : ∀ a. a → Maybe a
  ,  .ctor (∀[★] #0 -t> (#3 `@k #1))
  -- Nothing : ∀ a. Maybe a
  ,  .ctor (∀[★] #1 `@k #0)
  -- Maybe : ★ → ★
  , .datatype  (★ -k> ★)

  , .datatype  (★ -k> ★ -k> ★)
]
#eval wf_ctx test

#eval eval_ctx_loop test (((refl! (∀[★]#4 `@k #0))) `@c[refl! #0])
#eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[refl! #0] `@c[refl! #0])
#eval (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[sym! (refl! #0)] `@c[sym! (refl! #0)])
#eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[ ((sym! ((refl! (#3 `@k #0)).!2)) `; sym! ((refl! (#3 `@k #0))).!2)] `@c[sym! (refl! #0)])
#eval eval_ctx_loop test (sym! ((refl! (#3 `@k #0)).!2))

def test1 : Ctx Term := [
  .term (∀[★] #0 -t> #1) (Λ[★] `λ[#0] #0)
]
#eval wf_ctx test1

-- #eval infer_kind [] (∀[★] #0 -t> #1)
-- #eval infer_type [] (Λ[★] `λ[#0] #0)
-- #eval wf_kind ★

-- #eval infer_type [.kind ★] (`λ[#0] #0)
-- #eval infer_kind [.kind ★] (#0) -- some ★
-- #eval is_type ★
-- #eval infer_type [(.type #0) , .kind ★] (#0)
-- #eval is_type (#0 -t> #1)
