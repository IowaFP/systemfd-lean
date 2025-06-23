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


def MonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl ((`★ `-k> `★) `-k> `★)
  .nil
  .nil
  [-- ∀ m a b. Monad m. m a → (a → b) → m b
    `∀{(`★ `-k> `★)} `∀{`★} `∀{`★} ((`#2 `•k `#1) → (`#2 → `#2) → (`#4 `•k `#2))
   -- ∀ m a. Monad m ⇒ a → m a
  , `∀{(`★ `-k> `★)} `∀{`★} (`#0 → `#2 `•k `#1)
  ]

-- class StateMonad s m | m -> s
def StateMonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> (`★ `-k> `★) `-k> `★)
    [`#5 `•k `#0] -- ∀ s m. StateMonad s m -> Monad m
    [ ([0] , 1) ] -- m ~> s  ∀ s1 s2 m. StateMonad s1 m -> StateMonad s2 m -> (s1 ~ s2)
    .nil -- oms

def Γ := StateMonadFrame ::
         MonadFrame ::
         EqCtx

#eval "StateMonad, monad, Ord, Eq, Bool"
#eval Γ
#eval! DsM.run (compile_ctx Γ)
#eval! DsM.run (do
  let ctx <- compile_ctx Γ
  .toDsMq (wf_ctx ctx))


-- #eval! wf_ctx
-- [-- .openm (∀[★]∀[★]∀[★ -k> ★]#4 `@k #1 `@k #0 -t> #5 `@k #3 `@k #1 -t> (#3 ~[★]~ #4)),
--  .openm (∀[★ -k> ★]∀[★]#2 `@k #0 `@k #1 -t> #6 `@k #2),
--  .opent (★ -k> (★ -k> ★) -k> ★),
--  .openm (∀[★ -k> ★]∀[★]#3 `@k #1 -t> #1 -t> #3 `@k #2),
--  .openm (∀[★ -k> ★]∀[★]∀[★]#3 `@k #2 -t> #3 `@k #2 -t> (#3 -t> #3) -t> #5 `@k #3),
--  .opent ((★ -k> ★) -k> ★),
--  .openm (∀[★]#2 `@k #0 -t> #1 -t> #2 -t> #8),
--  .openm (∀[★]#1 `@k #0 -t> #1 -t> #2 -t> #7),
--  .opent (★ -k> ★),
--  .ctor #1,
--  .ctor #0,
--  .datatype ★]
