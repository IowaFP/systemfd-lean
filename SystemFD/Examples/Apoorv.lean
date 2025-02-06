import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

notation t1 ";;" t2 => t1 (t2)
notation t1 "::" t2 => Term.cons t1 t2

def booltest : Term :=
  -- unit type
  Term.letdata ★   -- Unit : ★,
  ;; letctor! #0 -- unit : Unit
  -- boolean
  ;; Term.letdata  ★  -- Bool : ★
  ;; letctor! #0 -- False : Bool
  ;; letctor! #1 -- True : Bool

  -- Maybe
  ;; Term.letdata (★ -k> ★)             -- Maybe : ★ → ★
  ;; letctor! (∀[★] #1 `@k #0)          -- Nothing : ∀ (a : ★). Maybe a
  ;; letctor! (∀[★] #0 -t> (#2 `@k #1)) -- Just : ∀ (a : ★). a → Maybe a

  -- Either
  ;; Term.letdata (★ -k> ★ -k> ★) -- Either : ★ → ★ → ★
  ;; letctor! (∀[★] ∀[★] #1 -t> (#2 `@k #1 `@k #0)) -- Left : ∀ (a : ★). a → Either a b
  ;; letctor! (∀[★] ∀[★] #0 -t> (#3 `@k #1 `@k #0)) -- Right : ∀ (a : ★). b → Either a b

  -- identity function ∀ a. a → a
  ;; Term.letterm (∀[★] #0 -t> #0) (Λ[★] `λ[#0] #0)
  ;; #0

def boolCtx : Ctx Term := mkCtx [] booltest

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
