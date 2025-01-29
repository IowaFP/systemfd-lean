
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
  -- Eq : ★ → ◯
  ;; Term.letopentype (★ -k> ◯)
  ;; Term.letopen (∀[★] #1 `@k #0 -t> #0 -t> #0 -t> #11)
  ;; #11
