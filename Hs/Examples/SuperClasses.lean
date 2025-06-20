import Hs.HsTerm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

-- import Hs.Examples.Datatypes
-- import Hs.Examples.Classes

def BoolCtx : HsCtx HsTerm :=
  [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                     , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                     ]
  ]

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

def EqCFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
         .nil
         .nil
         [ `∀{`★} `#0 → `#1 → `#6    -- TODO: make type class predicate implicit?
         , `∀{`★} `#0 → `#1 → `#7 ]

def EqCtx : HsCtx HsTerm :=
  EqCFrame :: BoolCtx


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
    [ `∀{`★} (`#0 → `#1 → `#13)
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
#eval! DsM.run (compile_ctx supCtx)
#eval! DsM.run (
  do let ctx <- compile_ctx supCtx
     .toDsMq (wf_ctx ctx))
def ex1 : HsTerm := (`#10 `•t `#14 `• (.HsHole (`#11 `•k `#14))) -- `• `#13 `• `#12

def ex1' : Term := (#10 `@t #14 `@ (#8 `@t #14 `@ refl! ★ #14)) `@ #13 `@ #12

#eval! DsM.run (
  do let Γ <- compile_ctx supCtx
     let t := (`#10 `•t `#14 `• (.HsHole (`#11 `•k `#14)) `• `#13 `• `#13)
     let t' <- compile Γ #14 t
     .toDsMq (infer_type Γ t') -- should be #14
     )
