import Hs.HsTerm
-- import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

-- def idHsType : HsTerm := `∀{`★} `#0 → `#1
-- def idHsTerm : HsTerm := Λ̈[`★] λ̈[`#0] `#0

-- unsafe def idType := compile [] ★ idHsType
-- unsafe def idTerm := do { let ty <- idType; compile [] ty idHsTerm }

-- #guard idType == .some (∀[★] #0 -t> #1)
-- #guard idTerm == .some (Λ[★]`λ[#0] #0)
-- #guard idType == do { let t <- idTerm; infer_type [] t }

-- #eval! idType
-- #eval! idTerm



def BoolCtx : HsCtx HsTerm :=
  [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                     , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                     ]
  ]
-- #eval! compile_ctx BoolCtx

def MbCtx : HsCtx HsTerm :=
  [ .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                               , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                               ]
  ]

#eval "Maybe Datatype"
#eval! compile_ctx MbCtx
