
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx

notation t1 ";;" t2 => t1 (t2)
notation t1 "::" t2 => Term.cons t1 t2

def booltest : Term :=
  -- unit type
  Term.letdata ★ 1   -- Unit : ★,
  ;; Term.letctor #0 -- unit : Unit
  -- boolean
  ;; Term.letdata  ★ 2  -- Bool : ★
  ;; Term.letctor #0 -- False : Bool
  ;; Term.letctor #1 -- True : Bool

  -- Maybe
  ;; Term.letdata (★ -k> ★) 2       -- Maybe : ★ → ★
  ;; Term.letctor (∀[★] #1 `@k #0)  -- Nothing : ∀ (a : ★). Maybe a
  ;; Term.letctor (∀[★] #0 -t> (#2 `@k #0)) -- Just : ∀ (a : ★). a → Maybe a

  -- Either
  ;; Term.letdata (★ -k> ★ -k> ★) 2 -- Either : ★ → ★ → ★
  ;; Term.letctor (∀[★] ∀[★] #1 -t> (#2 `@k #1 `@k #0)) -- Left : ∀ (a : ★). a → Either a b
  ;; Term.letctor (∀[★] ∀[★] #0 -t> (#3 `@k #1 `@k #0)) -- Right : ∀ (a : ★). b → Either a b

  -- identity function ∀ a. a → a
  ;; Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)

  -- not : Bool -> Bool
  ;; Term.letterm (#9 -t> #9)
       (`λ[ #9 ] (Term.case (#0)
              (Term.branch #9 0 #8)
            :: Term.branch #8 0 #9)
        )

  -- class Eq t where (==) : t → t → Bool

  -- Eq : ★ → ◯
  ;; Term.letopentype (★ -k> ◯)
  -- == : ∀ t. Eq t → t → t → Bool
  ;; Term.letopen (∀[★] (#1 `@k #0) -t> (#0 -t> #0 -t> #11))
  -- EqBool : ∀ t. t ~ Bool → Eq t
  ;; Term.insttype (∀[★] #0 ~ #12 -t> #2 `@k #0)

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
        (Term.case #0
            (Term.branch #14 0
              (Term.case #1
                (Term.branch #14 0 #14
                :: Term.branch #13 0 #13)))
        :: (Term.branch #13 0
              (Term.case #1
                (Term.branch #14 0 #13
                :: Term.branch #13 0 #14)))))

  -- instance Eq Bool where
  --    b1 == b2 = not (b1 `xor` b2)

  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. not b1 `xor` b2 ▹ sym c

  ;; Term.inst 2 (Λ[★] `λ[#0 ~ #12]
      Term.guard #3 1 #1 (#3 ▹ Term.sym (Term.arrowc #0 #0)))
  ;; #1
