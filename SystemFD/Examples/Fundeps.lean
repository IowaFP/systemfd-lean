import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def FundepsCtx : Ctx Term := [
  -- id :: ∀ a b. Equal a b -> a -> b =
  --     Λ a b. λ i a. a |> fdEqual1 a a b (EqualTT a a (refl a)) i
  .term (∀[★] ∀[★] (#7 `@k #1 `@k #0) -t> #2 -t> #2)
    (Λ[★] Λ[★] `λ[#7 `@k #1 `@k #0] `λ[#2]
      #0 ▹ (#8 `@t #3 `@t #3 `@t #2 `@ (#6 `@t #3 `@t #3 `@ refl! #3) `@ #1)),
  -- instance fdEqual2 = Λ t t' u. λ i1 i2.
  --     guard EqualTT[t, u] <- i1 then λ c1.
  --     guard EqualTT[t', u] <- i2 then λ c2.
  --         c1 ; sym c2
  .inst 2 (Λ[★] Λ[★] Λ[★] `λ[#7 `@k #2 `@k #0] `λ[#8 `@k #2 `@k #1]
    .guard (#6 `@t #4 `@t #2) #1 (`λ[#4 ~ #2]
      .guard (#7 `@t #4 `@t #3) #1 (`λ[#4 ~ #3]
        #1 `; sym! #0
  ))),
  -- instance fdEqual1 = Λ t u u'. λ i1 i2.
  --     guard EqualTT[t, u] <- i1 then λ c1.
  --     guard EqualTT[t, u'] <- i2 then λ c2.
  --         sym c1 ; c2
  .inst 2 (Λ[★] Λ[★] Λ[★] `λ[#6 `@k #2 `@k #1] `λ[#7 `@k #3 `@k #1]
    .guard (#5 `@t #4 `@t #3) #1 (`λ[#4 ~ #3]
      .guard (#6 `@t #5 `@t #3) #1 (`λ[#5 ~ #3]
        sym! #1 `; #0
  ))),
  -- instance EqualTT :: ∀ t u. t ~ u -> Equal t u
  .insttype (∀[★] ∀[★] #1 ~ #0 -t> #5 `@k #2 `@k #1),
  -- open fdEqual2 :: ∀ t t' u. Equal t u -> Equal t' u -> t ~ t'
  .openm (∀[★] ∀[★] ∀[★] (#4 `@k #2 `@k #0) -t> (#5 `@k #2 `@k #1) -t> #4 ~ #3),
  -- open fdEqual1 :: ∀ t u u'. Equal t u -> Equal t u' -> u ~ u'
  .openm (∀[★] ∀[★] ∀[★] (#3 `@k #2 `@k #1) -t> (#4 `@k #3 `@k #1) -t> #3 ~ #2),
  -- open Equal :: ★ -> ★ -> ★
  .opent (★ -k> ★ -k> ★)
]

#eval wf_ctx FundepsCtx
