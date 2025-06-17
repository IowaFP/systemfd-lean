import Hs.HsTerm
import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term
import SystemFD.Evaluator

-- import Hs.Examples.Datatypes
-- import Hs.Examples.Classes

def BoolF : HsFrame HsTerm :=
   .datatypeDecl `★ [ `#0     -- True
                    , `#1     -- False
                    ]

-- #eval! compile_ctx BoolCtx

def MbF : HsFrame HsTerm :=
   .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                              , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                              ]

def notT : HsFrame HsTerm :=
  .term (`#2 → `#3) (λ̈[`#2] .HsIte (.HsAnnotate `#3 `#2) (.HsAnnotate `#3 `#0) (.HsAnnotate `#3 `#1) `#2)

def eqBoolT : HsFrame HsTerm :=
  .term (`#3 → `#4 → `#5) (λ̈[`#3] λ̈[`#4] (.HsIte (.HsAnnotate `#5 `#3) (.HsAnnotate `#5 `#0)
                                                 (.HsAnnotate `#5 (.HsIte (.HsAnnotate `#5 `#3)
                                                                          (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#3) `#4))
                                                 ((.HsIte (.HsAnnotate `#5 `#4) (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#3) `#4))))

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

def EqCF : HsFrame HsTerm :=
  .classDecl (`★ `-k> `★)
         .nil
         .nil
         [ `∀{`★} (`#1 `•k `#0) ⇒ `#1 → `#2 → `#9    -- TODO: make type class predicate implicit?
         , `∀{`★} (`#2 `•k `#0) ⇒ `#1 → `#2 → `#10 ]

def EqBoolI : HsFrame HsTerm :=
  .inst (`#2 `•k `#7)
  [ `#4
  , .HsAnnotate (`#9 → `#10 → `#11) (λ̈[`#9]λ̈[`#10] (`#8 `• (`#7 `• `#0 `• `#1)))
  -- , .HsAnnotate (`#9 → `#10 → `#11) (λ̈[`#9]λ̈[`#10] (`#8 `• (`#2 `•t `#11 `• (.HsHole (`#6 `•k `#11)) `• `#0 `• `#1)))
  ]

/-
-- instance Eq a => Eq (Maybe a) where
--  ==  :
--  =/= :
-/
def EqMaybeI : HsFrame HsTerm :=
  .inst (`#9 `•k `#0 ⇒ `#10 `•k `#1)
  [ `#1
  , `#2
  ]

/-
eqMaybe : ∀ a Eq a => Maybe a → Maybe a → Bool
eqMaybe = Λ (a:★) λ (d : Eq a) λ m1 λ m2 ->
  case m1 of
    Nothing -> case m2 of
                  Nothing -> true
                  _       -> false
    Just x  -> case m2 of
                  Just y -> eq a d x y
                  Nohting -> false
-/

def eqMaybeTy := `∀{`★} (`#9 `•k `#0) ⇒ (`#4 `•k `#1) → (`#5 `•k `#2) → `#17
def eqMaybeT := Λ̈[`★] λ̈[`#9 `•k `#0]
  λ̈[`#4 `•k `#1] λ̈[`#5 `•k `#2]
     .HsIte (.HsAnnotate (`#6 `•k `#3) (`#5 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#1)
        (.HsAnnotate `#17 (.HsIte (.HsAnnotate (`#6 `•k `#3) (`#5 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#0)
               (.HsAnnotate `#17 `#16)   -- x = Nothing; y = Nothing
               `#15))                    -- x = Nothing; y ≠ Nothing
        (.HsIte (.HsAnnotate (`#3 → `#7 `•k `#4) (`#4 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#1)
             -- (.HsAnnotate (`#3 → `#18) (λ̈[`#3] `#17))
             (.HsAnnotate (`#3 → `#18) (λ̈[`#3]
                 (.HsIte (.HsAnnotate (`#4 → `#8 `•k `#5) (`#5 `•t `#4)) (.HsAnnotate (`#7 `•k `#4) `#1)
                         (.HsAnnotate (`#4 → `#19) (λ̈[`#4]
                             `#13 `•t `#5 `• `#4 `• `#1 `• `#0 -- (.HsHole (`#14 `•k `#5)) -- TODO fix this synth
                             ))   --x = Just x';y = Just y'
                         `#17)))  -- x = Just x'; y = Nothing
            `#16)


def eqMaybeF : HsFrame HsTerm := .term eqMaybeTy eqMaybeT

def Γ : HsCtx HsTerm := [
  -- EqMaybeI,
  -- eqMaybeF,
  MbF,
  EqBoolI,
  EqCF,
  eqBoolT,
  notT,
  BoolF ]


-- #eval "MaybeEq, Maybe, EqBool, Eq, Bool"
-- #eval Γ
#eval! compile_ctx Γ
#eval! do let Γ' <- compile_ctx Γ
          let τ <- compile Γ' ★ eqMaybeTy
          compile Γ' τ eqMaybeT

#eval! do let Γ' <- compile_ctx Γ
          let τ <- compile Γ' ★ eqMaybeTy
          let t' <- compile Γ' τ eqMaybeT
          infer_type Γ' t'

def Γ1 : HsCtx HsTerm := [
  -- EqMaybeI,
  eqMaybeF,
  MbF,
  EqBoolI,
  EqCF,
  eqBoolT,
  notT,
  BoolF ]


#eval! compile_ctx Γ1

-- #eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
--           let t <- compile Γ #4 (`#0 `• `#3 `• `#3)
--           .some (eval_ctx_loop Γ t) -- `#3

-- #eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
--           let t <- compile Γ #4 (`#0 `• `#3 `• `#2)
--           .some (eval_ctx_loop Γ t) -- `#2

-- #eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
--           let t <- compile Γ #4 (`#1 `• `#3)
--           .some (eval_ctx_loop Γ t) -- `#2

-- #eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
--           let t <- compile Γ #4 (`#1 `• `#2)
--           .some (eval_ctx_loop Γ t) -- `#3
