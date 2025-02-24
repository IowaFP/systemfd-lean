
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
-- import SystemFD.Algorithm
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

      .inst #2
            (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
               Term.guard (#3 `@t #1) -- EqBool[t]
               #0                     -- i
                -- λ (tBool : t ~ Bool).  ==@Bool ▹ sym! (tBool -c> tBool -c> rfl Bool)
               (`λ[#1 ~ #8]
                     (#3 ▹ sym! (#0 -c> (#1 -c> refl! #11)))))

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
  , .opent (★ -k> ★)

  -- True : Bool
  , .ctor #1
    -- False : Bool
  , .ctor #0
  -- Bool : ★
  , .datatype ★
]

-- #eval wf_ctx EqBoolCtx
-- #eval infer_type EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #5) -- some 7

-- == [Bool] (EqBool[Bool] refl) True True ⟶★ True
#eval eval_ctx_loop EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #5) -- some 5
-- == [Bool] (EqBool[Bool] refl) True False ⟶★ False
#eval eval_ctx_loop EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #6) -- some 6
