
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def ctx : Ctx Term := [
    -- f : ∀ t. F Int t → t → t
    --   = Λ t λd.
    --     let h = fdF[Int][Bool][t](FIB [Int][Bool] <Int> <Bool>) d in
    --     not ▹ <→> `@c h `@c h
    .term (∀[★] (#9 `@k #10 `@k #9) -t> #1 -t> #2)
      (Λ[★]`λ[#8 `@k #9 `@k #0]
        Term.letterm ((#15 ~ #1)) (#10 `@t #12 `@t #15 `@t  #1 `@ (#11 `@t #12 `@t #15 `@t #1) `@ #0) (
        #2 ▹ (#0 -c> #0))
      )

    --  not : Bool → Bool → Bool
    --      = λ x y. if x ← True then if y ← True then True
    --                                else if x ← False then True
    --                                else False
   , .term (#12 -t> #13 -t> #14)
           (`λ[#12]`λ[#13]
             Term.ite #10 #1 (Term.ite #10 #0 #10
                             (Term.ite #11 #1 #10 #11))
                             (#11))

  --   Λ t u v. λ d1 d2.
  --     If FMM[t][u] ← d1 then Λ a' b'. λ h1 h2 e1.
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ k1 k2 e2.
  --     let j : (a' ~ a'') = (h1 ; sym k1).2 in
  --     let e1' : F a'' b = e1 ▹ <Maybe> `@c j `@c <b'> in
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] e1' e2 ; k2
  , .inst #6
      (Λ[★]Λ[★]Λ[★]  `λ[#10 `@k #2 `@k  #1]  `λ[#11 `@k #3 `@k #2]
        Term.guard  (#5 `@k #4 `@k #3)  #1 (Λ[★]Λ[★]`λ[(#6 `@k #1) ~ #3]`λ[(#7 `@k #1) ~ #3]`λ[(#12 `@k #3 `@k #2)]
        Term.guard  (#5 `@k #4 `@k #3) #5 (Λ[★]Λ[★] `λ[(#11 `@k #6) ~ #8]`λ[(#13`@k #7) ~ #9]`λ[(#19 `@k #10 `@k #9)]
        Term.letterm (#9 ~ #4) (#7 `; sym! #2) (
        Term.letterm (#23 `@k #5 `@k #9) (#6 ▹ (∀c[★]refl! #24  `@c #1 `@c (refl! #5))) (
        sym! #8 `; (refl! #19 -c> #24 `@k #5 `@k #10 `@k #6) `; #3
            )))))

  -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  , .insttype (∀[★]∀[★]∀[★]∀[★]
                (#6 `@k #1 ~ #3) -t> (#7 `@k #1 ~ #3) -t> (#12 `@k #3 `@k #2) -t> (#13 `@k #6 `@k #5))

  -- Just : ∀ a. a → Maybe a
  , .ctor (∀[★] #0 -t> (#3 `@k #1))
  -- Nothing : ∀ a. Maybe a
  , .ctor (∀[★] #1 `@k #0)
  -- Maybe : ★ → ★
  , .datatype (★ -k> ★)

  -- fdf : Λ t u v. λ d1 d2.
  --       If FIB[t][u] ← d1 then λ h1 h2
  --       If FIB[t][v] ← d2 then λ k1 k2
  --          (sym h2) ; k2
  , .inst #1 (Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #2]
                (Term.guard (#5 `@k #4 `@k #3) #1 (`λ[#8 ~ #4] `λ[#12 ~ #4]
                 Term.guard (#7 `@k #6 `@k #4) #2 (`λ[#10 ~ #6] `λ[#14 ~ #5] ((sym! #2) `; (#0))))
                )
           )

  -- FIB : ∀ t u. Int ~ t → Bool ~ u → F t u
  , .insttype (∀[★]∀[★] (#4 ~ #1) -t> (#8 ~ #1) -t> (#5 `@k #3 `@k #2))

  -- -- fdF : ∀ t u v. F t u → F t v → u ~ v
  , .openm (∀[★]∀[★]∀[★] (#3 `@k #2 `@k #1) -t> (#4 `@k #3 `@k #1) -t> (#3 ~ #2))

  -- F : ★ → ★ → ★
  , .opent (★ -k> ★ -k> ★)


  , .datatype ★ -- Int : ★

  , .ctor #1 -- True : Bool
  , .ctor #0 -- False : Bool
  , .datatype  ★   -- Bool : ★
]

#eval wf_ctx ctx

-- #eval infer_type ctx (#0)
-- #eval infer_kind ctx (∀[★]∀[★]∀[★] (#3 `@k #2 `@k #1) -t> (#4 `@k #3 `@k #1) -t> (#3 ~ #2))
-- #eval infer_type ctx (Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #1]
--                           (Term.guard (#5 `@k #4 `@k #3) #1 (`λ[#8 ~ #4] `λ[#12 ~ #4]
--                           Term.guard (#7 `@k #6 `@k #4) #2 (`λ[#10 ~ #6] `λ[#14 ~ #5] ((sym! #2) `; (#0)))))
--                      )
-- /-
-- not : Bool -> Bool
-- not = λ x → case x of
--                False → True
--                True → False
--                _ → False
-- -/
-- def notTerm : Term :=
--        (`λ[ #2 ] Term.ite
--                   #2 -- False
--                   #0 -- x
--                   #1 -- True
--                   (Term.ite
--                     #1
--                     #0
--                     #2
--                     #2 -- False catch all
--                   ))
-- /-      eqBool = λ x. λ y. case x of
--                             True → case y of
--                                     True → True
--                                     False → False
--                             False → case y of
--                                     True → False
--                                     False → True
--  -/
-- def eqBoolTerm : Term :=
--      `λ[#2] `λ[#3]
--         (Term.ite #2 #1 (Term.ite #2 #0 #2 #3)
--         (Term.ite #3 #1 (Term.ite #3 #0 #2 #3)
--           #3))

-- -- #eval eqBoolTerm
-- -- #eval notTerm

-- -- #eval infer_type boolCtx notTerm

-- -- #eval eval_ctx_loop boolCtx (notTerm `@ #1)
-- -- #eval eval_ctx_loop boolCtx (notTerm `@ #0)

-- -- #eval infer_type boolCtx eqBoolTerm
-- -- #eval eval_ctx_loop boolCtx (eqBoolTerm `@ #1 `@ #1)
-- -- #eval eval_ctx_loop boolCtx (eqBoolTerm `@ #0 `@ #1)


-- def EqBoolCtx : Ctx Term := [

--   -- instance (==)[t] i
--   --    If EqBool[t] tBool ← i
--   --        let c = refl @ tBool @ (refl @ tBool @ refl) in
--   --        λb1. λb2. ==@Bool ▹ sym c

--       .inst #2
--             (Λ[★] `λ[#4 `@k #0] -- EqBool : Eq t
--                Term.guard (#3 `@t #1) -- EqBool[t]
--                #0                     -- i
--                 -- λ (tBool : t ~ Bool).  ==@Bool ▹ sym! (tBool -c> tBool -c> rfl Bool)
--                (`λ[#1 ~ #8]
--                      (#3 ▹ sym! (#0 -c> (#1 -c> refl! #11)))))

--     -- ==@Bool : Bool → Bool → Bool
--     /-   eqBool = λ x. λ y. case x of
--                             True → case y of
--                                     True → True
--                                     False → False
--                             False → case y of
--                                     True → False
--                                     False → True
--     -/
--     , .term (#5 -t> (#6 -t> #7))
--      (`λ[#5] `λ[#6]
--         (Term.ite #5 #1 (Term.ite #5 #0 #5 #6)
--         (Term.ite #6 #1 (Term.ite #6 #0 #5 #6)
--           #6)))

--   -- EqBool : ∀ t. t ~ Bool → Eq t
--   , .insttype (∀[★] (#0 ~ #5) -t> #3 `@k #1)

--   -- == : ∀ t. Eq t → t → t → Bool
--   , .openm (∀[★] (#1 `@k #0) -t> (#1 -t> (#2 -t> #7)))

--   -- Eq : ★ → ◯
--   , .opent (★ -k> ★)

--   -- True : Bool
--   , .ctor #1
--     -- False : Bool
--   , .ctor #0
--   -- Bool : ★
--   , .datatype ★
-- ]

-- #eval wf_ctx EqBoolCtx
-- #eval infer_type EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #5) -- some 7

-- -- == [Bool] (EqBool[Bool] refl) True True ⟶★ True
-- #eval eval_ctx_loop EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #5) -- some 5
-- -- == [Bool] (EqBool[Bool] refl) True False ⟶★ False
-- #eval eval_ctx_loop EqBoolCtx (#3 `@t #7 `@ (#2 `@t #7 `@ refl! #7) `@ #5 `@ #6) -- some 6
