import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

notation t1 ";;" t2 => t1 (t2)
notation t1 "::" t2 => Term.cons t1 t2

def booltest : Term :=
  -- unit type
  Term.letdata ★ 1   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  -- boolean
  ;; Term.letdata  ★ 2  -- Bool : ★
  ;; letctor! #0 -- False : Bool
  ;; letctor! #1 -- True : Bool

  -- Maybe
  ;; Term.letdata (★ -k> ★) 2       -- Maybe : ★ → ★
  ;; letctor! (∀[★] #1 `@k #0)  -- Nothing : ∀ (a : ★). Maybe a
  ;; letctor! (∀[★] #0 -t> (#2 `@k #0)) -- Just : ∀ (a : ★). a → Maybe a

  -- Either
  ;; Term.letdata (★ -k> ★ -k> ★) 2 -- Either : ★ → ★ → ★
  ;; letctor! (∀[★] ∀[★] #1 -t> (#2 `@k #1 `@k #0)) -- Left : ∀ (a : ★). a → Either a b
  ;; letctor! (∀[★] ∀[★] #0 -t> (#3 `@k #1 `@k #0)) -- Right : ∀ (a : ★). b → Either a b

  -- identity function ∀ a. a → a
  ;; Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)

  -- not : Bool -> Bool
  ;; Term.letterm (#9 -t> #9)
       (`λ[ #9 ] Term.ite
                  #8 -- False
                  #0 -- x
                  #7 -- True
                  (Term.ite
                    #7
                    #0
                    #8
                    #8 -- False catch all
                  )

       )

  -- class Eq t where (==) : t → t → Bool

  -- Eq : ★ → ◯
  ;; letopentype! (★ -k> ◯)

  -- == : ∀ t. Eq t → t → t → Bool
  ;; letopen! (∀[★] (#1 `@k #0) -t> (#0 -t> #0 -t> #11))

  -- EqBool : ∀ t. t ~ Bool → Eq t
  ;; insttype! (∀[★] #0 ~ #12 -t> #2 `@k #0)

  -- eqBool : Bool → Bool → Bool
/-      eqBool = λ x. λ y. case x of
                            True → case y of
                                    True → True
                                    False → False
                            False → case y of
                                    True → False
                                    False → True
 -/
/-   ;; Term.letterm (#13 -t> #13 -t> #13)
     (`λ[#13] `λ[#14]
        (Term.case #0
            (Term.branch #14 0
              (Term.case #1
                (Term.branch #14 0 #14
                :: Term.branch #13 0 #13)))
        :: (Term.branch #13 0
              (Term.case #1
                (Term.branch #14 0 #13
                :: Term.branch #13 0 #14)))))
 -/
  -- instance Eq Bool where
  --    b1 == b2 = not (b1 `xor` b2)

  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. not b1 `xor` b2 ▹ sym c

 /-   ;; Term.inst 2 (Λ[★] `λ[#0 ~ #12]
      Term.guard (#3 `@k #1) /- EqBool[t]-/
                 #2 /-i-/
                 (`λ[#0 ~ #12] #3 ▹ sym! ( #0 -c> #0)))
 -/
/-   ;; #0 `@t #16 `@ #15 `@ #15
 -/
;; #3 `@ #11

def unitType : Term :=
  Term.letdata ★ 1   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; #1 -- ((Λ[★]`λ[#0] #0) `@t #1) `@ #0

def unit : Term :=
  Term.letdata ★ 1   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; #0 -- ((Λ[★]`λ[#0] #0) `@t #1) `@ #0

def unitRefl : Term :=
  Term.letdata ★ 1   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; (#0 ▹ refl! #1) -- () ▹ refl

def unitletterm : Term :=
  Term.letdata ★ 1   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
 -- identity function ∀ a. a → a
  ;; Term.letterm #1 #0
  ;; #0

def ident : Term :=
 -- identity function ∀ a. a → a
  Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)
  ;; #0

#eval infer_kind [.ctor #0 , .datatype ★ 1] #1
#eval infer_type .prf ([], unit)
#eval infer_type .prf ([], unitletterm)
#eval infer_type .prf ([], Λ[★] `λ[#0] #0)
#eval infer_type .prf ([], ident)
