import Hs.HsTerm
import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

def idHsType : HsTerm := `∀{`★} `#0 → `#1
def idHsTerm : HsTerm := Λ̈[`★] λ̈[`#0] `#0

unsafe def idType := compile [] ★ idHsType
unsafe def idTerm := do { let ty <- idType; compile [] ty idHsTerm}

-- #guard idType == .some (∀[★] #0 -t> #1)
-- #guard idTerm == .some (Λ[★]`λ[#0] #0)
-- #guard idType == do { let t <- idTerm; infer_type [] t }

#eval! idType
#eval! idTerm



def BoolCtx : HsCtx HsTerm :=
  [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                     , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                     ]
  ]
#eval! compile_ctx BoolCtx

def MbCtx : HsCtx HsTerm :=
  [ .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                               , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                               ]
  ]
#eval! compile_ctx MbCtx


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

#eval! compile_ctx EqCtx

def EqBoolInst : HsFrame HsTerm := .inst
  (`#2 `•k `#5)
  .nil

#eval! compile_ctx (EqBoolInst :: EqCtx)



def OrdCFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
    [`#3 `•k `#0]
    .nil
    [ `∀{`★} (`#2 `•k `#0) ⇒ (`#1 → `#2 → `#12) -- TODO: make type class predicate implicit?
    ]

def MonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl ((`★ `-k> `★) `-k> `★)
  .nil
  .nil
  [`∀{(`★ `-k> `★)} `∀{`★} `∀{`★} (`#3 `•k `#2) ⇒ ((`#4 `•k `#3) → (`#4 → `#4) → (`#6 `•k `#4))
    -- ∀ m a b. Monad m. m a → (a → b) → m b
  , `∀{(`★ `-k> `★)} `∀{`★} (`#3 `•k `#1) ⇒ (`#1 → (`#3 `•k `#2)) -- ∀ m a. Monad m ⇒ a → m a

  ]

-- class StateMonad s m
def StateMonadFrame : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> (`★ `-k> `★) `-k> `★)
    [`#6 `•k `#1] -- ∀ s m. StateMonad s m -> Monad m
    [ ([0] , 1) ] -- m ~> s
    .nil -- oms

#eval! compile_ctx (StateMonadFrame :: MonadFrame :: OrdCFrame :: EqCtx)
