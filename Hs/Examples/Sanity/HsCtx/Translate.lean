import Hs.Translator

namespace HsCtx.Test.Translator

def BF : HsFrame HsTerm :=
   .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                    , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                    ]


def MBCtx : HsFrame HsTerm :=
   .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                              , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                              ]


def ctx : HsCtx HsTerm := [MBCtx, BF]
#eval ctx

def ctx' := compile_ctx ctx

@[simp]
def check_compile_ctx_aux : HsCtx HsTerm -> DsM (List (FrameMetadata HsTerm × Frame Term)) := λ Γ => do
  let Γ' <- compile_ctx Γ
  return (List.map (λ i => (Γ s@ i, Γ' s@ i)) (Term.shift_helper (Γ'.length)))

@[simp]
def check_frame_equiv (Γ : Ctx Term) : FrameMetadata HsTerm -> Frame Term -> DsM Bool
| .empty, .empty => return true
| .tycon k, .datatype k' => do
  let k'' <- compile_kind Γ □ k
  return k'' == k'
| .datacon τ, .ctor τ' => do
  let τ'' <- compile_type Γ ★ τ
  return τ'' == τ'
| .type τ, .type τ' => do
  let τ'' <- compile_type Γ ★ τ
  return τ'' == τ'
| _, _ => return false



@[simp]
def check_compile_ctx : HsCtx HsTerm -> DsM Bool := λ Γ => do
  let ΓΓ' <- check_compile_ctx_aux Γ
  let Γ' <- compile_ctx Γ
  let x <- List.allM (λ x => check_frame_equiv Γ' x.1 x.2) ΓΓ'
  return Γ'.length == Γ.length && x


#eval DsM.run (check_compile_ctx_aux ((HsFrame.datatypeDecl `★ [`#0]) :: .nil))

-- #eval DsM.run ctx'
-- #eval ctx

#eval DsM.run (check_compile_ctx_aux ctx)


-- #eval DsM.run (check_compile_ctx_aux ((HsFrame.datatypeDecl `★ .nil) :: .nil))

-- #eval DsM.run (check_compile_ctx_aux ((HsFrame.datatypeDecl `★ [`#0]) :: .nil))

#guard check_compile_ctx ((HsFrame.datatypeDecl `★ .nil) :: .nil) == DsM.ok true


-- #eval DsM.run (compile_ctx [HsFrame.datatypeDecl `★ [ `#0 ]])

#guard check_compile_ctx ((HsFrame.datatypeDecl `★ [`#0]) :: .nil) == DsM.ok true

#guard check_compile_ctx ctx == DsM.ok true


-- #eval (ctx s@ 0)
-- #eval DsM.run (do let c <- ctx'; return (c d@ 4))
-- #eval (ctx s@ 4)



end HsCtx.Test.Translator
