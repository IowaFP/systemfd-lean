import Hs.HsTerm
-- import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

def idHsType : HsTerm := `∀{`★} `#0 → `#1
def idHsTerm : HsTerm := Λ̈[`★] λ̈[`#0] `#0

unsafe def idType := compile [] ★ idHsType
unsafe def idTerm := do { let ty <- idType; compile [] ty idHsTerm }

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

def dtctx : HsCtx HsTerm := MbCtx ++ BoolCtx

#eval "Maybe Datatype"

-- #eval! compile_ctx dtctx

-- #eval! do let Γ <- compile_ctx dtctx
--           wf_ctx Γ

#eval! do let Γ <- compile_ctx dtctx
          let τ <- compile Γ ★ idHsType
          -- compile Γ τ idHsTerm

          -- compile Γ τ (.HsAnnotate idHsType idHsTerm)
          -- let t <- compile Γ (#5) (((.HsAnnotate (`#5 → `#6) (λ̈[`#5] `#0))) `• `#4)
          -- infer_type Γ t
          -- compile Γ (#5 -t> #6) (((.HsAnnotate idHsType idHsTerm)) `•t `#5)
          -- compile Γ #5 `#4
          -- compile Γ #5 (((.HsAnnotate idHsType idHsTerm)) `•t `#5 `• `#4)
          -- instantiate_type (#5 -t> #6) #4
          let (h, args) <- (((.HsAnnotate idHsType idHsTerm)) `•t `#5 `• `#4).neutral_form
          -- .some (h, args)
          let h' <- compile Γ τ h
          let (tele, ret_ty) := τ.to_telescope
          .some (tele, ret_ty, args)
          -- .some h'
