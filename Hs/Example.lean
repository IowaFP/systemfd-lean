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

#eval! compile [.datatype (★ -k> ★)] ★ (`∀{`★} (`#1 `•k `#0))
#eval! compile [.kind ★, .datatype (★ -k> ★)] ★ (`#1 `•k `#0)
#eval HsTerm.split_kind_app (`#1 `•k `#0)
#eval ([.kind ★, .datatype (★ -k> ★)] d@ 1).get_type
#eval Term.split_kind_arrow [] (★ -k> ★)

  -- let (h, sp) <- split_kind_app (.HsCtor2 .appk f a)
  -- let τ <- (Γ d@ h).get_type
  -- let (κs, κ') <- split_kind_arrow [] τ
  -- let args' <- List.mapM
  --   (λ a => compile Γ a.1 a.2)
  --   (List.zip κs sp)

  -- .some (mk_kind_app h args')


#eval! compile_ctx MbCtx
