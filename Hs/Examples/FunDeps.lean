import Hs.HsTerm
import Hs.Algorithm
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


def OrdCFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
    [`#4 `•k `#0]
    .nil
    [ `∀{`★} (`#2 `•k `#0) ⇒ (`#1 → `#2 → `#11) -- TODO: make type class predicate implicit?
    ]

def MonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl ((`★ `-k> `★) `-k> `★)
  .nil
  .nil
  [-- ∀ m a b. Monad m. m a → (a → b) → m b
    `∀{(`★ `-k> `★)} `∀{`★} `∀{`★} (`#3 `•k `#2) ⇒ ((`#3 `•k `#2) → (`#3 → `#3) → (`#5 `•k `#3))
   -- ∀ m a. Monad m ⇒ a → m a
  , `∀{(`★ `-k> `★)} `∀{`★} (`#3 `•k `#1) ⇒ (`#1 → `#3 `•k `#2)
  ]

-- class StateMonad s m | m -> s
def StateMonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> (`★ `-k> `★) `-k> `★)
    [`#5 `•k `#1] -- ∀ s m. StateMonad s m -> Monad m
    [ ([0] , 1) ] -- m ~> s  ∀ s1 m s2. StateMonad s1 m -> StateMonad s2 m
    .nil -- oms

#eval "StateMonad, monad, Ord, Eq, Bool"
#eval StateMonadFrame :: MonadFrame :: OrdCFrame :: EqCtx
#eval! compile_ctx (StateMonadFrame :: MonadFrame :: OrdCFrame :: EqCtx)
#eval! do let ctx <- compile_ctx (StateMonadFrame :: MonadFrame :: OrdCFrame :: EqCtx)
          wf_ctx ctx
