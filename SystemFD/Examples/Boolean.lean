
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

/-
not : Bool -> Bool
not = λ x → case x of
               False → True
               True → False
               _ → False
-/
def notTerm : Term :=
       (`λ[ #2 ] Term.ite
                  #2 -- False
                  #0 -- x
                  #1 -- True
                  (Term.ite
                    #1
                    #0
                    #2
                    #2 -- False catch all
                  ))
/-      eqBool = λ x. λ y. case x of
                            True → case y of
                                    True → True
                                    False → False
                            False → case y of
                                    True → False
                                    False → True
 -/
def eqBoolTerm : Term :=
     `λ[#2] `λ[#3]
        (Term.ite #2 #1 (Term.ite #2 #0 #2 #3)
        (Term.ite #3 #1 (Term.ite #3 #0 #2 #3)
          #3))

-- #eval eqBoolTerm
-- #eval notTerm

-- #eval infer_type boolCtx notTerm

-- #eval eval_ctx_loop boolCtx (notTerm `@ #1)
-- #eval eval_ctx_loop boolCtx (notTerm `@ #0)

-- #eval infer_type boolCtx eqBoolTerm
-- #eval eval_ctx_loop boolCtx (eqBoolTerm `@ #1 `@ #1)
-- #eval eval_ctx_loop boolCtx (eqBoolTerm `@ #0 `@ #1)


def EqBoolCtx : Ctx Term := [

  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. ==@Bool ▹ sym c

      .inst 2
            (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
               Term.guard (#3 `@k #1) -- EqBool[t]
               #0                     -- i
                -- λ (tBool : t ~ Bool).  ==@Bool ▹ sym! (tBool -c> tBool -c> rfl Bool)
               (`λ[#1 ~ #8] (#3 ▹ sym! (#0 -c> (#0 -c> refl! #9)))))

    -- ==@Bool : Bool → Bool → Bool
    /-   eqBool = λ x. λ y. case x of
                            True → case y of
                                    True → True
                                    False → False
                            False → case y of
                                    True → False
                                    False → True
    -/
   , .term (#5 -t> (#6 -t> #7))
     (`λ[#5] `λ[#6]
        (Term.ite #5 #1 (Term.ite #5 #0 #5 #6)
        (Term.ite #6 #1 (Term.ite #6 #0 #5 #6)
          #6)))

  -- EqBool : ∀ t. t ~ Bool → Eq t
  , .insttype (∀[★] (#0 ~ #5) -t> #3 `@k #1)

  -- == : ∀ t. Eq t → t → t → Bool
  , .openm (∀[★] (#1 `@k #0) -t> (#1 -t> (#2 -t> #7)))

  -- Eq : ★ → ◯
  , .opent (★ -k> ◯)

  -- True : Bool
  , .ctor #1
    -- False : Bool
  , .ctor #0
  -- Bool : ★
  , .datatype ★
]

#eval wf_ctx EqBoolCtx
-- #eval infer_type EqBoolCtx #0
-- #eval infer_type EqBoolCtx (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
--                             Term.guard (#3 `@k #1) -- EqBool[t]
--                             #0                     -- i
--                            -- λ (tBool : t ~ Bool).  ==@Bool ▹ sym! (tBool -c> tBool -c> rfl Bool)
--                            (`λ[#1 ~ #8] (#3 ▹ sym! (#0 -c> (#0 -c> refl! #9)))))
#eval eval_ctx_loop EqBoolCtx (#3 `@t #7 `@ (#2 `@k #7 `@ refl! #7) `@ #5 `@ #5)

def t1 := eval_inst EqBoolCtx (#3 `@t #7 `@ (#2 `@k #7 `@ refl! #7) `@ #6 `@ #6)
#eval t1
def t2 := eval_inst EqBoolCtx t1[0]
#eval t2
def t3 := eval_inst EqBoolCtx t2[0]
#eval t3
def t4 := eval_inst EqBoolCtx t3[0]
#eval t4
def t5 := eval_inst EqBoolCtx t4[0]
#eval t5
def t6 := eval_inst EqBoolCtx t5[0]
#eval t6
def t7 := eval_inst EqBoolCtx t6[0]
#eval t7
def t8 := eval_inst EqBoolCtx t7[0]
#eval t8
def t9 := eval_inst EqBoolCtx t8[0]
#eval t9
def t10 := eval_inst EqBoolCtx t9[0]
#eval t10
def t11 := eval_inst EqBoolCtx t10[0]
#eval t11
def t12 := eval_inst EqBoolCtx t11[0]
#eval t12
#eval infer_type EqBoolCtx t9[0]
