import Hs.HsTerm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

import Hs.Examples.Datatypes
import Hs.Examples.Classes

-- def BoolCtx : HsCtx HsTerm :=
--   [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
--                      , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
--                      ]
--   ]

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

-- def EqCFrame : HsFrame HsTerm :=
--   HsFrame.classDecl (`★ `-k> `★)
--          .nil
--          .nil
--          [ `∀{`★} (`#1 `•k `#0) ⇒ `#1 → `#2 → `#7    -- TODO: make type class predicate implicit?
--          , `∀{`★} (`#2 `•k `#0) ⇒ `#1 → `#2 → `#8 ]

-- def EqCtx : HsCtx HsTerm :=
--   EqCFrame :: BoolCtx


def EqBoolI : HsFrame HsTerm := .inst
  (`#2 `•k `#5)
  [ .HsAnnotate (`#6 → `#7 → `#8) (λ̈[`#6] λ̈[`#7] `#7) -- fst method
  , .HsAnnotate (`#7 → `#8 → `#9) (λ̈[`#7] λ̈[`#8] `#7) -- second method
  ]

def OrdC : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
    [ `#7 `•k `#0
    ]
    .nil
    [ `∀{`★} (`#2 `•k `#0) ⇒ (`#1 → `#2 → `#14)
    ]


def OrdBool : HsFrame HsTerm :=
  HsFrame.inst
  (`#2 `•k `#11)
  [ .HsAnnotate (`#13 → `#14 → `#15) (λ̈[`#13] λ̈[`#14] `#14)

  ]

def supCtx := OrdBool ::
              OrdC ::
              EqBoolI ::
              EqCtx

#eval println! "OrdBool, Ord, EqBool, Bool"
#eval supCtx
#eval! compile_ctx supCtx
#eval! do let ctx <- compile_ctx supCtx
          wf_ctx ctx

def ex1 : HsTerm := (`#10 `•t `#14 `• (.HsHole (`#11 `•k `#14))) -- `• `#13 `• `#12

def ex1' : Term := (#10 `@t #14 `@ (#8 `@t #14 `@ refl! ★ #14)) `@ #13 `@ #12

-- #eval! do let ctx <- compile_ctx supCtx
--           synth_term ctx (#11 `@k #14)

#eval! do let Γ <- compile_ctx supCtx
          -- let τ <- (Γ d@ 10).get_type
          -- instantiate_type τ #14

          -- compile Γ (∀[★](#12 `@k #0) -t> #1 -t> #2 -t> #18) `#10

          -- compile Γ ((#11 `@k #14) -t> #15 -t> #16 -t> #17) (`#10 `•t `#14)
          -- compile Γ (#11 `@k #14) (.HsHole (`#11 `•k `#14))
          compile Γ #14 (`#10 `•t `#14 `• (.HsHole (`#11 `•k `#14)) `• `#13 `• `#13)
          -- compile Γ (#14 -t> #15 -t> #16) (.HsAnnotate (`#14 → `#15 → `#16) ex1)
