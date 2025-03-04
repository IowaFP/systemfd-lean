
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
#eval! wf_ctx boolCtx

def test : Ctx Term := [
    .datatype ★
  , .ctor (∀[★] #0 -t> (#3 `@k #1))  -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #1 `@k #0)           -- Nothing : ∀ a. Maybe a
  , .datatype  (★ -k> ★)             -- Maybe : ★ → ★

  , .ctor #1
  , .ctor #0
  , .datatype ★
]

#eval wf_ctx test

#eval stable_type_match test (#3 `@k #6) (#3 `@k #6)

#eval infer_type test (((refl! (∀[★]#4 `@k #0))) `@c[refl! #0])

#eval infer_type test (#2 `@t #6)
#eval infer_type test (#4)
#eval prefix_type_match test (#3 `@k #6) #6
#eval infer_type test (.ite (#2 `@t #6) (#2 `@t #6) (#4) (#4))


#eval infer_type test (#1 `@t #6 `@ #5)
#eval infer_type test (#1 `@t #6)
#eval infer_type test (`λ[#6] #0)
#eval infer_type test (.ite (#1 `@t #6) (#1 `@t #6 `@ #5) (`λ[#6] #0) (#4))


-- #eval eval_ctx_loop test (.ite (#1 `@t #6) (#1 `@t #6 `@ #5) (`λ[#6] #0) (`λ[#6] #0))

-- #eval eval_ctx_loop test (((refl! (∀[★]#4 `@k #0))) `@c[refl! #0])
-- #eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[refl! #0] `@c[refl! #0])
-- #eval (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[sym! (refl! #0)] `@c[sym! (refl! #0)])
-- #eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[ ((sym! ((refl! (#3 `@k #0)).!2)) `; sym! ((refl! (#3 `@k #0))).!2)] `@c[sym! (refl! #0)])
-- #eval eval_ctx_loop test (sym! ((refl! (#3 `@k #0)).!2))

def test1 : Ctx Term := [
  .term (∀[★] #0 -t> #1) (Λ[★] `λ[#0] #0)
]
#eval! wf_ctx test1


def test2 : Ctx Term := [
  .ctor #0,
  .datatype ★
]

#eval! wf_ctx test2

#eval! infer_type test2 (.letterm #1 #0 #1)
-- #eval infer_kind [] (∀[★] #0 -t> #1)
-- #eval infer_type [] (Λ[★] `λ[#0] #0)
-- #eval wf_kind ★

-- #eval infer_type [.kind ★] (`λ[#0] #0)
-- #eval infer_kind [.kind ★] (#0) -- some ★
-- #eval is_type ★
-- #eval infer_type [(.type #0) , .kind ★] (#0)
-- #eval is_type (#0 -t> #1)
