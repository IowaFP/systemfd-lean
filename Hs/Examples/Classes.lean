import Hs.HsTerm
-- import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

import Hs.Examples.Datatypes

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

def EqCFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
         .nil
         .nil
         [ `∀{`★} `#0 → `#1 → `#6
         , `∀{`★} `#0 → `#1 → `#7 ]

def EqCtx : HsCtx HsTerm :=
  EqCFrame :: BoolCtx


#eval DsM.run (compile_ctx EqCtx)
#guard (do let c <- compile_ctx EqCtx
           .toDsMq (wf_ctx c)) == .ok ()
