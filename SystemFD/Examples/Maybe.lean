
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def MaybeBoolCtx : Ctx Term := [
  /- Λ t. λ (i : Eq t).
       If EqMaybe[t] <- i.
         Λ u. λ (tmu : t ~ Maybe u). λ eqU : Eq u.
           eqMaybe ▹ sym (<t ~ Bool> → <t ~ Bool> → <Bool>)
    -/
    .inst #7 (Λ[★] `λ[#10 `@k #0] -- Λt. λ(i : Eq t)
                   .guard (#3 `@t #1) #0    --     EqMaybe[t] ← i
                    (Λ[★] `λ[#2 ~ (#7 `@k #0)] `λ[#13 `@k #1]  -- Λ u. λ (tmu : t ~ Maybe u). λ (eqU : Eq u)
                                                   -- eqMaybeU[u] eqU ▹ (t ~ Maybe u) → (t ~ Maybe u) → <Bool>
                                              (#5 `@t #2 `@ #0) ▹ sym! (#1 -c> #2  -c> refl! #19))


                   )

    , .term ((∀[★] (#9 `@k #0) -t> (#5 `@k #1) -t> (#6 `@k #2) -t> #15))
         ((Λ[★] `λ[#9 `@k #0] `λ[#5 `@k #1] `λ[#6 `@k #2]
                .ite (#6 `@t #3) #1
                     (.ite (#6 `@t #3) #0
                               #13    -- x = Nothing; y = Nothing
                               #14) ( -- x = Nothing; y ≠ Nothing
                .ite (#5 `@t #3) #1
                     (`λ[#3] (.ite (#7 `@t #4) #1
                                   #15  -- x = Just x'; y = Nothing
                              (.ite (#6 `@t #4) #1 -- x = Just x'; y = Just y'
                                   (`λ[#4] ((#13 `@t #5 `@ #4) `@ #1 `@ #0))
                                    #14)))
                #14)))

  -- EqMaybe : ∀ t u. t ~ Maybe u → Eq u → Eq t
   , .insttype (∀[★]∀[★] (#1 ~ (#4 `@k #0)) -t> (#10 `@k #1) -t> (#11 `@k #3))

  -- Just : ∀ a. a → Maybe a
  ,  .ctor (∀[★] #0 -t> (#3 `@k #1))
  -- Nothing : ∀ a. Maybe a
  , .ctor (∀[★] #1 `@k #0)
  -- Maybe : ★ → ★
  , .datatype  (★ -k> ★)


  , .inst #2 (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
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

  -- Eq : ★ → ★
  , .opent (★ -k> ★)

  -- True : Bool
  , .ctor #1
  -- False : Bool
  , .ctor #0
  -- Bool : ★
  , .datatype  ★
]

#eval wf_ctx MaybeBoolCtx


-- /-
-- isNothing : ∀ a. Maybe a → Bool
-- isNothing = Λ a. λ x:Maybe a. case x of
--                         Nothing → True
--                         Just y → False
-- -/
-- def isNothing : Term :=
--   Λ[★]`λ[#3 `@k #0]
--            .ite (#3 `@t #1) #0 #5
--           (.ite (#2 `@t #1) #0 (`λ[#1] #7) #6)

-- #eval isNothing
-- #eval infer_type MaybeBoolCtx isNothing

-- #eval infer_type MaybeBoolCtx ((isNothing `@t #5) `@ (#1 `@t #5))

-- #eval eval_ctx_loop MaybeBoolCtx ((isNothing `@t #5) `@ (#1 `@t #5))
-- #eval eval_ctx_loop MaybeBoolCtx ((isNothing `@t #5) `@ (#0 `@t #5 `@ #4))

#eval infer_type MaybeBoolCtx (#4 `@t #13) -- Nothing : Maybe Bool
#eval infer_type MaybeBoolCtx (#3 `@t #13 `@ #12) -- Just True : Maybe Bool

#eval eval_ctx_loop MaybeBoolCtx (#1 `@t #13 `@ (#8 `@t #13 `@ refl! #13) `@ (#4 `@t #13) `@ (#4 `@t #13))
#eval eval_ctx_loop MaybeBoolCtx (#1 `@t #13 `@ (#9 `@t #13 `@ refl! #13) `@ (#4 `@t #13) `@ (#3 `@t #13 `@ #12))

#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      infer_type MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! maybeBool) `@ (#8 `@t bool `@ refl! bool)))


-- == [Maybe Bool]
--           (EqMaybeU[Maybe Bool, Bool] <Maybe Bool> (EqBool[Bool] <Bool>)
--           Nothing Nothing) -- returns True
#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      eval_ctx_loop MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! maybeBool) `@ (#8 `@t bool `@ refl! bool))
          `@ (#4 `@t bool) `@ (#4 `@t bool ))
-- == [Maybe Bool]
--           (EqMaybeU[Maybe Bool, Bool] <Maybe Bool> (EqBool[Bool] <Bool>)
--           Nothing (Just False)

#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      eval_ctx_loop MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! maybeBool) `@ (#8 `@t bool `@ refl! bool))
          `@ (#4 `@t bool) `@ (#3 `@t bool `@ #12))
