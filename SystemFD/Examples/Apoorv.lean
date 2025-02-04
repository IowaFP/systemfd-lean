import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm

notation t1 ";;" t2 => t1 (t2)
notation t1 "::" t2 => Term.cons t1 t2

def booltest : Term :=
  -- unit type
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  -- boolean
  ;; Term.letdata  ★   -- Bool : ★
  ;; letctor! #0 -- False : Bool
  ;; letctor! #1 -- True : Bool

  -- Maybe
  ;; Term.letdata (★ -k> ★)       -- Maybe : ★ → ★
  ;; letctor! (∀[★] #1 `@k #0)  -- Nothing : ∀ (a : ★). Maybe a
  ;; letctor! (∀[★] #0 -t> (#2 `@k #0)) -- Just : ∀ (a : ★). a → Maybe a

  -- Either
  ;; Term.letdata (★ -k> ★ -k> ★) -- Either : ★ → ★ → ★
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
  ;; Term.letterm (#13 -t> #13 -t> #13)
     (`λ[#13] `λ[#14]
        (Term.ite #14 #1 (Term.ite #14 #0 #14 #15)
        (Term.ite #15 #1 (Term.ite #15 #0 #14 #15)
          #15)))

;; #4 `@ #13


def booltest2 : Term :=
  -- unit type
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  -- boolean
  ;; Term.letdata  ★  -- Bool : ★
  ;; letctor! #0 -- False : Bool
  ;; letctor! #1 -- True : Bool

  -- Maybe
  ;; Term.letdata (★ -k> ★)       -- Maybe : ★ → ★
  ;; letctor! (∀[★] #1 `@k #0)  -- Nothing : ∀ (a : ★). Maybe a
  ;; letctor! (∀[★] #0 -t> (#2 `@k #0)) -- Just : ∀ (a : ★). a → Maybe a

  -- Either
  ;; Term.letdata (★ -k> ★ -k> ★) -- Either : ★ → ★ → ★
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
  ;; Term.letterm (#13 -t> #13 -t> #13)
     (`λ[#13] `λ[#14]
        (Term.ite #14 #1 (Term.ite #14 #0 #14 #15)
        (Term.ite #15 #1 (Term.ite #15 #0 #14 #15)
          #15)))

  -- instance Eq Bool where
  --    b1 == b2 = not (b1 `xor` b2)

  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. not b1 `xor` b2 ▹ sym c

   ;; Term.inst 2 (Λ[★] `λ[#4 `@k #0]
      Term.guard (#3 `@k #1) -- EqBool[t]
                 #0 -- i
                 (`λ[#1 ~ #16] #3 ▹ sym! ( #0 -c> #0)))

   ;; #3 `@t #15 `@ (#3 `@k #15 `@ refl! #15)  `@ #14 `@ #14


def unitType : Term :=
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; #1 -- ((Λ[★]`λ[#0] #0) `@t #1) `@ #0

def unit : Term :=
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; #0 -- ((Λ[★]`λ[#0] #0) `@t #1) `@ #0

def unitRefl : Term :=
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)
  ;; (#0 `@t #2 `@ #1 ▹ ((∀c[◯]refl! #0) `@c refl! #0)) -- () ▹ refl

def unitletterm : Term :=
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  ;; Term.letterm #1 #0
  ;; #0

def ident : Term :=
 -- identity function ∀ a. a → a
  Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)
  ;; #0

#eval infer_kind [.ctor #0 , .datatype ★] #1
#eval infer_type [] unit
#eval infer_type [] unitletterm
#eval infer_type [] (Λ[★] `λ[#0] #0)
#eval infer_type [] ident
#eval infer_type [] booltest
#eval infer_type [] booltest2
#eval infer_type [] unitRefl


#eval Term.inst 2 (Λ[★] `λ[#4 `@k #0]
      Term.guard (#3 `@k #1) -- EqBool[t]
                 #0 -- i
                 (`λ[#1 ~ #16] #3 ▹ sym! ( #0 -c> #0))) ;; #0
