
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def MaybeBoolCtx : Ctx Term := [
    .ctor #1       -- True : Bool
  , .ctor #0       -- False : Bool
  , .datatype  ★   -- Bool : ★

  , .ctor (∀[★] #0 -t> (#3 `@k #1)) -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #1 `@k #0) -- Nothing : ∀ a. Maybe a
  , .datatype  (★ -k> ★)   -- Maybe : ★ → ★
]


/-
isNothing : ∀ a. Maybe a → Bool
isNothing = Λ a. λ x:Maybe a. case x of
                        Nothing → True
                        Just y → False
-/
def isNothing : Term :=
  Λ[★] `λ[#6 `@t #0]
       .ite #6 #0 (Λ[#1] #3)
       (.ite #5 #0 (Λ[#1]`λ[#0] #5) #2)

#eval wf_ctx MaybeBoolCtx
#eval isNothing
#eval infer_type MaybeBoolCtx isNothing

#eval infer_type MaybeBoolCtx (#4 `@t #2) -- Nothing : Maybe Bool
#eval infer_type MaybeBoolCtx (#3 `@t #2 `@ #0) -- Just True : Maybe Bool

#eval! infer_type MaybeBoolCtx ((isNothing `@t #2) `@ (#4 `@t #2))

#eval! eval_ctx_loop MaybeBoolCtx [((isNothing `@t #2) `@ (#4 `@t #2))]
#eval! eval_ctx_loop MaybeBoolCtx [((isNothing `@t #2) `@ (#3 `@t #2 `@ #0))]
