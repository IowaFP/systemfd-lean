
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def MaybeBoolCtx : Ctx Term := [
    .ctor (∀[★] #0 -t> (#3 `@k #1)) -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #1 `@k #0) -- Nothing : ∀ a. Maybe a
  , .datatype  (★ -k> ★)   -- Maybe : ★ → ★

  , .ctor #1       -- True : Bool
  , .ctor #0       -- False : Bool
  , .datatype  ★   -- Bool : ★
]

#eval wf_ctx MaybeBoolCtx

-- def MaybeBoolCtx' : Ctx Term := [
--     .ctor (#4 -t> (#2 `@k #5)) -- Just : Maybe Bool
--   , .ctor (#0 `@k #3) -- Nothing : Maybe Bool
--   , .datatype  (★ -k> ★)   -- Maybe : ★ → ★

--   , .ctor #1       -- True : Bool
--   , .ctor #0       -- False : Bool
--   , .datatype  ★   -- Bool : ★
-- ]

-- #eval wf_ctx MaybeBoolCtx'


-- def isNothingBool : Term :=
--   `λ[#2 `@k #5] .ite #2 #0 #4
--                 (.ite #1 #0 (`λ[#6] #6) #4)

--        -- (.ite #5 #0 (0] #5) #3)
-- #eval infer_type MaybeBoolCtx' isNothingBool

/-
isNothing : ∀ a. Maybe a → Bool
isNothing = Λ a. λ x:Maybe a. case x of
                        Nothing → True
                        Just y → False
-/
def isNothing : Term :=
  Λ[★]`λ[#3 `@k #0]
           .ite (#3 `@t #1) #0 #5
          (.ite (#2 `@t #1) #0 (`λ[#1] #7) #6)

#eval isNothing
#eval infer_type MaybeBoolCtx isNothing

#eval infer_type MaybeBoolCtx (#1 `@t #5) -- Nothing : Maybe Bool
#eval infer_type MaybeBoolCtx (#0 `@t #5 `@ #3) -- Just True : Maybe Bool

#eval infer_type MaybeBoolCtx ((isNothing `@t #5) `@ (#1 `@t #5))

#eval eval_ctx_loop MaybeBoolCtx ((isNothing `@t #5) `@ (#1 `@t #5))
#eval eval_ctx_loop MaybeBoolCtx ((isNothing `@t #5) `@ (#0 `@t #5 `@ #4))
