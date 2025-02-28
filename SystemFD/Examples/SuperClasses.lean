
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def OrdEqBoolCtx : Ctx Term := [

     /- Λ a. λ (d: Ord a).
          OrdBool[a] ← d | λ (h : a ~ Bool)
          (λ x y. not x || y) ▹ (h -c> (h -c> <Bool>))
     -/
     .inst #5 (Λ[★] `λ[#7 `@k #0]
       Term.guard (#5 `@t #1) #0 (`λ[#1 ~ #16]
         (`λ[#17] `λ[#18] (#6 `@ (#5 `@ #1) `@ #0)) ▹ ((sym! #0) -c> ((sym! #1) -c> refl! #19))
       )),

    -- not : Bool → Bool
     .term (#13 -t> #14) (`λ[#13] Term.ite #12 #0 #13 #12) ,
    -- or : Bool → Bool → Bool
     .term (#12 -t> #13 -t> #14) (`λ[#12] `λ[#13] Term.ite #12 #1 #12 (Term.ite #13 #1 #0 #13)),
     -- Λa λ (d: Ord a). OrdBool[a] ← #0 then EqBool[a]
     .inst #1 (Λ[★] `λ[#4 `@k #0] Term.guard (#2 `@t #1) #0 (#8 `@t #1)),
     .insttype (∀[★](#0 ~ #11) -t> (#4 `@k #1)), -- OrdBool : ∀ t. t ~ Bool → Ord t
     .openm (∀[★] (#2 `@k #0) -t> (#8 `@k #1)), -- eqSuperOrd : ∀ t. Ord t → Eq t
     .openm (∀[★] (#1 `@k #0) -t> #1 -t> #2 -t> #12), -- < : ∀ t : Ord t → t → t → Bool
     .opent (★ -k> ★), -- Ord : ★ → ★
  -- instance (==)[t] i
      .inst #2 (Λ[★] `λ[#4 `@k #0]
               Term.guard (#3 `@t #1) #0 (`λ[#1 ~ #8]
                     (#3 ▹ sym! (#0 -c> (#1 -c> refl! #11)))))
    -- ==@Bool : Bool → Bool → Bool
    , .term (#5 -t> (#6 -t> #7))
     (`λ[#5] `λ[#6]
        (Term.ite #5 #1 (Term.ite #5 #0 #5 #6)
        (Term.ite #6 #1 (Term.ite #6 #0 #5 #6)
          #6)))

  , .insttype (∀[★] (#0 ~ #5) -t> #3 `@k #1)   -- EqBool : ∀ t. t ~ Bool → Eq t
  , .openm (∀[★] (#1 `@k #0) -t> (#1 -t> (#2 -t> #7)))   -- == : ∀ t. Eq t → t → t → Bool
  , .opent (★ -k> ★)   -- Eq : ★ → ◯
  , .ctor #1   -- True : Bool
  , .ctor #0    -- False : Bool
  , .datatype ★   -- Bool : ★
]

#eval wf_ctx OrdEqBoolCtx

-- leq : ∀ a. Ord a → a → a → Bool
-- leq = Λ a. λ (d: Ord a). λ x y. ((<) [a] d x y) || (== [a] (ordEq [a] d) x y)

def leq := Λ[★] `λ[#8 `@k #0] `λ[#1] `λ[#2] (
   #6
   `@ (#10  `@t #3 `@ #2 `@ #1 `@ #0)
   `@ (#15 `@t #3 `@ (#9 `@t #3 `@ #2) `@ #1 `@ #0)
 )

#eval infer_type OrdEqBoolCtx leq
