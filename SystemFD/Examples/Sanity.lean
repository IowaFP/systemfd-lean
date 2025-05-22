
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

#guard (wf_ctx boolCtx == .some ())

def test : Ctx Term := [
    .datatype ★
  , .ctor (∀[★] #0 -t> (#3 `@k #1))  -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #1 `@k #0)           -- Nothing : ∀ a. Maybe a
  , .datatype  (★ -k> ★)             -- Maybe : ★ → ★

  , .ctor #1
  , .ctor #0
  , .datatype ★
]

#guard (wf_ctx test == .some ())

-- #eval stable_type_match test (#3 `@k #6) (#3 `@k #6)
#guard (stable_type_match test (#3 `@k #6) (#3 `@k #6) == .some ())

-- #eval infer_type test (((refl! (∀[★]#4 `@k #0))) `@c[refl! #0])
#guard (infer_type test (((refl! ★ (∀[★]#4 `@k #0))) `@c[refl! ★ #0]) == .some ((#3 `@k #0) ~[★]~ (#3 `@k #0)))

#eval infer_type test (#2 `@t #6)
#guard (infer_type test (#2 `@t #6) == .some (#3 `@k #6))

#eval infer_type test (#4)
#guard (infer_type test (#4) == .some (#6))

#eval prefix_type_match test (#3 `@k #6) #6
#guard (prefix_type_match test (#3 `@k #6) #6 == .some #6)

#eval infer_type test (.ite (#2 `@t #6) (#2 `@t #6) (#4) (#4))
#guard (infer_type test (.ite (#2 `@t #6) (#2 `@t #6) (#4) (#4)) == .some #6)

#eval infer_type test (#1 `@t #6 `@ #5)
#guard (infer_type test (#1 `@t #6 `@ #5) == .some (#3 `@k #6))

#eval infer_type test (#1 `@t #6)
#guard (infer_type test  (#1 `@t #6) == .some (#6 -t> (#4 `@k #7)))

#eval infer_type test (`λ[#6] #0)
#guard (infer_type test (`λ[#6] #0) == .some (#6 -t> #7))

#eval infer_type test (.ite (#1 `@t #6) (#1 `@t #6 `@ #5) (`λ[#6] #0) (#4))
#guard (infer_type test (.ite (#1 `@t #6) (#1 `@t #6 `@ #5) (`λ[#6] #0) (#4)) == .some #6)

-- #eval eval_ctx_loop test (.ite (#1 `@t #6) (#1 `@t #6 `@ #5) (`λ[#6] #0) (`λ[#6] #0))

-- #eval eval_ctx_loop test (((refl! (∀[★]#4 `@k #0))) `@c[refl! #0])
-- #eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[refl! #0] `@c[refl! #0])
-- #eval (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[sym! (refl! #0)] `@c[sym! (refl! #0)])
-- #eval eval_ctx_loop test (((refl! (∀[★]∀[★]#6 `@k #1 `@k #0))) `@c[ ((sym! ((refl! (#3 `@k #0)).!2)) `; sym! ((refl! (#3 `@k #0))).!2)] `@c[sym! (refl! #0)])
-- #eval eval_ctx_loop test (sym! ((refl! (#3 `@k #0)).!2))

def test1 : Ctx Term := [
  .term (∀[★] #0 -t> #1) (Λ[★] `λ[#0] #0)
]
#eval wf_ctx test1
#guard (wf_ctx test1 == .some ())


def test2 : Ctx Term := [
  .ctor #0,
  .datatype ★
]

#eval wf_ctx test2
#guard (wf_ctx test2 == .some ())

#eval infer_type test2 (.letterm #1 #0 #1)
#guard (infer_type test2 (.letterm #1 #0 #1) == .some #1)


#eval eval_ctx_loop test2 (`0 `@ #0)
