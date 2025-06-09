import Hs.HsTerm
import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

import Hs.Examples.Datatypes

-- def BoolCtx : HsCtx HsTerm :=
--   [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
--                      , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
--                      ]
--   ]

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

def EqCFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
         .nil
         .nil
         [ `∀{`★} (`#1 `•k `#0) ⇒ `#1 → `#2 → `#7    -- TODO: make type class predicate implicit?
         , `∀{`★} (`#2 `•k `#0) ⇒ `#1 → `#2 → `#8 ]

def EqCtx : HsCtx HsTerm :=
  EqCFrame :: BoolCtx

#eval! do let c <- compile_ctx EqCtx
          wf_ctx c
