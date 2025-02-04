import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

-- notation t1 ";;" t2 => t1 (t2)
-- notation t1 "::" t2 => Term.cons t1 t2

namespace Term
  @[simp]
  def succ : Term -> Term
  | .var x => var (x + 1)
  | t => t

  @[simp]
  def add : Term -> Nat -> Term
  | .var x, k => .var (x + k)
  | t, _ => t
end Term

def NatCtx : Ctx Term := [
    -- instance fix = Λ a. λ i. guard (Fix a) <- i then λ f. f (fix i f)
    .inst 0 (Λ[★] `λ[#3 `@k #0] `λ[#1 -t> #2]
      .guard (#4 `@t #2) #1
        (#0 `@ (#3 `@t #2 `@ #1 `@ #0))),
    -- .inst 0 (Λ[★] `λ[#3 `@k #0]
    --   .guard (#3 `@t #1) #0
    --     (`λ[#1 -t> #1] #0 `@ (#2 `@ #1 `@ #0))),
    -- open fix : ∀ a, Fix a -> (a -> a) -> a
    .openm (∀[★] #2 `@k #0 -t> (#1 -t> #2) -t> #2),
    -- instance Fix : ∀ a, Fix a
    .insttype (∀[★] #1 `@k #0),
    -- open Fix : ★ -> ◯
    .opent (★ -k> ◯),
    -- Nat.succ
    .ctor (#1 -t> #2),
    -- Nat.zero
    .ctor #0, -- Nat.zero
    -- Nat
    .datatype ★
  ]

  -- #3 : [S' 4](∀[★] #2 `@k #0 -t> (#1 -t> #2) -t> #2)
  --    : ∀[★] #6 `@k #0 -t> (#1 -t> #2) -t> #2
  -- #2 : ★
  -- #1 : [S' 2](#3 `@k #0)
  --    : #5 `@k #2
  -- #0 : [S](#1 -t> #2)
  --    : #2 -t> #3

def ex_succ : Term := #0


  -- #3 `@t #2 : (#6 `@k #0 -t> (#1 -t> #2) -t> #2) β[#2]
  --           : #5 `@k #2 -t> (#3 -t> #4) -t> #4

  -- #3 `@t #2 `@ #1 : ((#3 -t> #4) -t> #4) β[.kind]
  --                 : (#2 -t> #3) -t> #3

  -- #3 `@t #2 `@ #1 `@ #0 : #3 β[.kind] = #2

def fixi := #0
def ofixi := fixi.succ
def Fixi := ofixi.succ
def oFixi := Fixi.succ
def succi := oFixi.succ
def zeroi := succi.succ
def Nati := zeroi.succ

def ex_pred : Term := `λ[Nati]
  .ite (zeroi.succ) #0 #0
  (.ite (succi.succ) #0 (`λ[Nati.succ] #0) #0)

#eval wf_ctx NatCtx
#eval infer_type NatCtx ex_pred
#eval infer_type NatCtx ex_succ
#eval! infer_type NatCtx (ex_pred `@ (ex_succ `@ #1))


#eval! eval_ctx_loop NatCtx [ex_pred]
#eval! eval_ctx_loop NatCtx [ex_pred `@ (ex_succ `@ #1)]


#eval! eval_ctx_loop NatCtx [ex_pred `@ (ex_succ `@ (ex_succ `@ #1))]
