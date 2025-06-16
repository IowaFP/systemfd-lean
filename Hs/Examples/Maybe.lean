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
  , `#5
  ]

def Γ : HsCtx HsTerm := [ -- EqIF ,
                          -- EqCF,
                          -- MbF,
                          EqBoolI,
                          EqCF,
                          eqBoolT,
                          notT,
                          BoolF ]

#eval "MaybeEq, Maybe, EqBool, Eq, Bool"
#eval Γ
#eval! compile_ctx Γ
#eval! do let Γ' <- compile_ctx Γ
          wf_ctx Γ'

#eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
          let t <- compile Γ #4 (`#0 `• `#3 `• `#3)
          .some (eval_ctx_loop Γ t) -- `#3

#eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
          let t <- compile Γ #4 (`#0 `• `#3 `• `#2)
          .some (eval_ctx_loop Γ t) -- `#2

#eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
          let t <- compile Γ #4 (`#1 `• `#3)
          .some (eval_ctx_loop Γ t) -- `#2

#eval! do let Γ <- compile_ctx [eqBoolT, notT, BoolF ]
          let t <- compile Γ #4 (`#1 `• `#2)
          .some (eval_ctx_loop Γ t) -- `#3
