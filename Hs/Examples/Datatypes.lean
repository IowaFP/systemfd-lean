import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term

def idHsType : HsTerm := `∀{`★} `#0 → `#1
def idHsTerm : HsTerm := Λ̈[`★] λ̈[`#0] `#0

def idType := compile [] ★ idHsType
def idTerm := do { let ty <- idType; compile [] ty idHsTerm }


def BoolCtx : HsCtx HsTerm :=
  [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                     , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                     ]
  ]

def MbCtx : HsCtx HsTerm :=
  [ .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                               , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                               ]
  ]

def dtctx : HsCtx HsTerm := MbCtx ++ BoolCtx

#guard (
  do let Γ <- compile_ctx dtctx
     .toDsMq (wf_ctx Γ)) == .ok ()
