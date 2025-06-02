import Hs.HsTerm
import Hs.Algorithm
import SystemFD.Algorithm

def idHsType : HsTerm := `∀{`★} `#0 → `#1
def idHsTerm : HsTerm := Λ̈[`★] λ̈[`#0] `#0

def idType := compile [] ★ idHsType
def idTerm := compile [] idType idHsTerm

-- #guard idType == .some (∀[★] #0 -t> #1)
-- #guard idTerm == .some (Λ[★]`λ[#0] #0)
-- #guard idType == do { let t <- idTerm; infer_type [] t }

#eval! idType
#eval! idTerm

-- def MbCtx : Ctx HsTerm :=
--   [ .ctor (`∀{`★} `#2 `•k `#0)          -- Nothing :: ∀ a. Maybe a
--   , .ctor (`∀{`★} `#0 → `#2 `•k `#1)    -- Just :: ∀ a. a -> Maybe a
--   , .datatype (`★ `-k> `★) ]
