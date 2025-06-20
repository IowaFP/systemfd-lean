
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
    .inst #8 (Λ[★] `λ[#10 `@k #0] -- Λt. λ(i : Eq t)
                .guard (#3 `@t #1) #0    --     EqMaybe[t] ← i
                (Λ[★] `λ[#2 ~[★]~ (#7 `@k #0)] `λ[#13 `@k #1] -- Λ u. λ (tmu : t ~ Maybe u). λ (eqU : Eq u)
                      -- eqMaybeU[u] eqU ▹ (t ~ Maybe u) → (t ~ Maybe u) → <Bool>
                       (#5 `@t #2 `@ #0) ▹ sym! (#1 -c> #2  -c> refl! ★ #19))


                   )
    -- ∀ a. Eq a →  Maybe a → Maybe a → Bool
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
   , .insttype (∀[★]∀[★] (#1 ~[★]~ (#4 `@k #0)) -t> (#10 `@k #1) -t> (#11 `@k #3))
  -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #0 -t> (#3 `@k #1))
  -- Nothing : ∀ a. Maybe a
  , .ctor (∀[★] #1 `@k #0)
  -- Maybe : ★ → ★
  , .datatype (★ -k> ★)

  , .inst #2 (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
               Term.guard (#3 `@t #1) #0 (`λ[#1 ~[★]~ #8] -- i
                -- λ (tBool : t ~ Bool).  ==@Bool ▹ sym! (tBool -c> tBool -c> rfl Bool)
                     (#3 ▹ sym! (#0 -c> (#1 -c> refl! ★ #11)))))

    -- ==@Bool : Bool → Bool → Bool
    /-   eqBool = λ x. λ y. case x of
                            True → case y of
                                    True → True
                                    False → False
                            False → case y of
                                    True → False
                                    False → True
    -/
  , .term (#5 -t> (#6 -t> #7)) (`λ[#5] `λ[#6]
        (Term.ite #5 #1 (Term.ite #5 #0 #5 #6)
        (Term.ite #6 #1 (Term.ite #6 #0 #5 #6)
         #6)))
  , .insttype (∀[★] (#0 ~[★]~ #5) -t> #3 `@k #1)   -- EqBool : ∀ t. t ~ Bool → Eq t
  , .openm (∀[★] (#1 `@k #0) -t> (#1 -t> (#2 -t> #7)))   -- == : ∀ t. Eq t → t → t → Bool
  , .opent (★ -k> ★)   -- Eq : ★ → ★
  , .ctor #1   -- True : Bool
  , .ctor #0  -- False : Bool
  , .datatype  ★   -- Bool : ★
]

#eval wf_ctx MaybeBoolCtx
#guard (wf_ctx MaybeBoolCtx == .some ())

#eval infer_type MaybeBoolCtx (#4 `@t #13) -- Nothing : Maybe Bool
#guard (infer_type MaybeBoolCtx (#4 `@t #13) == .some (#5 `@k #13))

#eval infer_type MaybeBoolCtx (#3 `@t #13 `@ #12) -- Just True : Maybe Bool
#guard (infer_type MaybeBoolCtx (#3 `@t #13 `@ #12) == .some (#5 `@k #13))



#eval! eval_ctx_loop MaybeBoolCtx (#1 `@t #13 `@ (#8 `@t #13 `@ refl! ★ #13) `@ (#4 `@t #13) `@ (#4 `@t #13))
#eval! eval_ctx_loop MaybeBoolCtx (#1 `@t #13 `@ (#9 `@t #13 `@ refl! ★ #13) `@ (#4 `@t #13) `@ (#3 `@t #13 `@ #12))

#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      infer_type MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! ★ maybeBool) `@ (#8 `@t bool `@ refl! ★ bool)))

-- == [Maybe Bool]
--           (EqMaybeU[Maybe Bool, Bool] <Maybe Bool> (EqBool[Bool] <Bool>)
--           Nothing Nothing) -- returns True
#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      eval_ctx_loop MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! ★ maybeBool) `@ (#8 `@t bool `@ refl! ★ bool))
          `@ (#4 `@t bool) `@ (#4 `@t bool ))


/-

(
  (
  (((#1)[#13] ⬝  ((#8)[#13] ⬝  (refl! ★; #13))) ▹

    (sym! (refl! ★; (#5 `@k #13)) → (refl! ★; (#6 `@k #14)) → (refl! ★; #15))

    ) ⬝  (#4)[#13]) ⬝

    ((#3)[#13] ⬝  #12))

-/


-- == [Maybe Bool]
--           (EqMaybeU[Maybe Bool, Bool] <Maybe Bool> (EqBool[Bool] <Bool>)
--           Nothing (Just False)
#eval let bool := #13;
      let maybe := #5
      let maybeBool := maybe `@k bool;
      eval_ctx_loop MaybeBoolCtx
      (#9 `@t maybeBool
          `@ (#2 `@t maybeBool `@t bool `@ (refl! ★ maybeBool) `@ (#8 `@t bool `@ refl! ★ bool))
          `@ (#4 `@t bool) `@ (#3 `@t bool `@ #12))
