import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def NatCtxFix : Ctx Term := [
  -- let two : Nat := succ (succ zero)
  .term #6 (#4 `@ (#4 `@ #5)),
  -- let add : Nat -> Nat -> Nat := fix (Nat -> Nat -> Nat) add_rec
  .term (#5 -t> #6 -t> #7)
    (#2 `@t (#5 -t> #6 -t> #7) `@ #0),
  -- let add_rec : (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat :=
  --   λ rec n m. ite zero <- n then m
  --     else ite succ <- n then λ x. succ (rec x m)
  --     else m
  .term ((#4 -t> #5 -t> #6) -t> #5 -t> #6 -t> #7)
    (`λ[#4 -t> #5 -t> #6] `λ[#5] `λ[#6]
      .ite #6 #1 #0 (
        .ite #5 #1 (`λ[#7] #6 `@ (#3 `@ #0 `@ #1))
        #0)),
  -- instance fix = Λ a. λ f. f (fix i f)
  .inst #0 (Λ[★] `λ[#0 -t> #1] (#0 `@ (#2 `@t #1 `@ #0))),
  -- open fix : ∀ a, (a -> a) -> a
  .openm (∀[★] (#0 -t> #1) -t> #1),
  -- Nat.succ
  .ctor (#1 -t> #2),
  -- Nat.zero
  .ctor #0,
  -- Nat
  .datatype ★
]


#eval wf_ctx NatCtxFix
#eval infer_type NatCtxFix (#1 `@ #0 `@ #0)

#eval infer_type NatCtxFix (((#4 `@t (#7 -t> #8 -t> #9)) `@ #2) `@ (#5 `@ #6) `@ #0)
#eval eval_ctx_loop NatCtxFix (((#4 `@t (#7 -t> #8 -t> #9)) `@ #2) `@ (#5 `@ #6) `@ #0)

def NatCtxDirect : Ctx Term := [

    /- ==@Nat := λ x λ y.
                  case x of
                    Zero → case y of
                            Zero → True
                            _ → False
                    Suc → λ x'. case y of
                            Zero → False
                            Succ →  λ y'. ==@Nat x' y'
   -/
   .inst #0 ( `λ[#9] `λ[#10]
      .ite #10 #1 (.ite #10 #0 #3 -- x = 0; y = 0
                               #4 -- x = 0; y ≠ 0
                                )
      (.ite #9 #1 (`λ[#11]
                    .ite #11 #1 #5 -- x = S n; y = 0
                   (.ite #10 #1 (`λ[#12] #4 `@ #1 `@ #0)  -- -- x = S n; y = S n'
                                #5))
           #4))

   -- ==@Nat : Nat → Nat → Bool
  , .openm (#8 -t> #9 -t> #4)

  , .ctor #1 -- True
  , .ctor #0 -- False
  , .datatype ★ -- Bool

  -- let two : Nat := succ (succ zero)
  , .term #4 (#2 `@ (#2 `@ #3))
  -- instance add : λ n.
  --   ite zero <- n then λ m. m
  --     else ite succ <- n then λ x. λ m. succ (add x m)
  --     else m
  , .inst #0 (`λ[#3]
    .ite #3 #0 (`λ[#4] #0) (
      .ite #2 #0 (`λ[#4] `λ[#5] #4 `@ (#3 `@ #1 `@ #0))
      (`λ[#4] #0)))
  -- open add : Nat -> Nat -> Nat
  , .openm (#2 -t> #3 -t> #4)
  -- Nat.succ
  , .ctor (#1 -t> #2)
  -- Nat.zero
  , .ctor #0
  -- Nat
  , .datatype ★
]


#eval eval_ctx_loop NatCtxDirect (#1 `@ (#7 `@ #5 `@ #5) `@ (#7 `@ #5 `@ #5)) -- (2 + 2) =? (2 + 2)

#eval eval_ctx_loop NatCtxDirect (#1 `@ #5 `@ (#8 `@ #9))


#eval wf_ctx NatCtxDirect
#eval infer_type NatCtxDirect (#7 `@ #5 `@ #5)

#eval eval_ctx_loop NatCtxDirect (#7 `@ #5 `@ #5)

-- #eval infer_type NatCtxDirect (#1 `@ #5 `@ #5)
-- #eval infer_type NatCtxDirect (#1 `@ #5 `@ (#8 `@ #9))
