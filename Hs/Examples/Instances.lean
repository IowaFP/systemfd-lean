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

-- #eval! compile_ctx EqCtx

def EqBoolInst : HsFrame HsTerm := .inst
  (`#2 `•k `#5)
  [ .HsAnnotate (`#6 → `#7 → `#8) (λ̈[`#6] λ̈[`#7] `#7)
  , .HsAnnotate (`#7 → `#8 → `#9) (λ̈[`#7] λ̈[`#8] `#7)
  ]

#eval! DsM.run (compile_ctx (EqBoolInst :: EqCtx))
#eval! DsM.run (
  do let ctx <- compile_ctx (EqBoolInst :: EqCtx)
     .toDsMq (wf_ctx ctx))
