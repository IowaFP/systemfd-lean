import Hs.HsTerm
import Hs.Algorithm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

def FCls : HsFrame HsTerm := .classDecl (`★ `-k> `★ `-k> `★) -- F t u
    .nil
    [([1],0)] --- t ~> u
    .nil


def FInst : HsFrame HsTerm := .inst (`#8 `•k `#2 `•k `#2)  .nil


def FDCtx : HsCtx HsTerm := [
  -- .inst (`#11 `•k `#9 `•k `#9)  .nil,
  .term (`#4 → `#5 → `#6) (λ̈[`#4]λ̈[`#5]`#5),
  FInst,
  .datatypeDecl `★ [`#0, `#1],
  .datatypeDecl `★ [`#0, `#1, `#2],
  FCls
]

#eval DsM.run (compile_ctx FDCtx)
#eval DsM.run (do
  let Γ' <- compile_ctx FDCtx
  .toDsMq (wf_ctx Γ'))

-- ∀ α. F Bool α ⇒ α → α → α
def τ := `∀{`★} `#12 `•k `#6 `•k `#0 ⇒ `#1 → `#2 → `#3
def t := Λ̈[`★]λ̈[`#12 `•k `#6 `•k `#0] `#2

#eval  DsM.run (do
       let Γ' <- compile_ctx FDCtx
       let τ' <- compile Γ' ★ τ
       compile Γ' τ' t
       )

-- #eval  DsM.run (do
--   let Γ <- compile_ctx [.datatypeDecl `★ .nil, .datatypeDecl `★ .nil, FCls]
--   let τ := `#3 `•k `#0  `•k `#1
--   let τ' <- compile Γ ★ τ
--   mk_inst_type Γ τ'
--   )


-- def Γ0 : Ctx Term :=  [
--  .insttype (∀[★]∀[★](#0 ~[★]~ #3) -t> (#2 ~[★]~ #3) -t> #7 `@k #2 `@k #3),
--  .datatype ★,
--  .datatype ★,
--  .openm (∀[★]∀[★]∀[★]#3 `@k #1 `@k #0 -t> #4 `@k #2 `@k #3 -t> (#2 ~[★]~ #4)),
--  .opent (★ -k> ★ -k> ★)
-- ]

-- def t : Term :=  Λ[★]Λ[★]Λ[★]`λ[#7 `@k #1 `@k #0]
--       `λ[#8 `@k #2 `@k #3]
--        -- .guard (#5 `@t #3 `@t #2) #1
--          (`λ[(#2 ~[★]~ #7)] `λ[(#4 ~[★]~ #7)]
--           -- .guard (#7 `@t #5 `@t #6) #2
--               (`λ[(#6 ~[★]~ #9)] `λ[(#6 ~[★]~ #9)]
--               (refl! ★ #6) `;
--               #3 `;
--               (sym! #1)))
-- #eval (wf_ctx Γ0)
-- -- #eval infer_type Γ0 t
-- #eval do
--        let Γ : Ctx Term := [
--        .insttype (∀[★]∀[★](#0 ~[★]~ #3) -t> (#2 ~[★]~ #3) -t> #7 `@k #2 `@k #3),
--        .datatype ★,
--        .datatype ★,
--        .openm (∀[★]∀[★]∀[★]#3 `@k #1 `@k #0 -t> #4 `@k #2 `@k #3 -t> (#2 ~[★]~ #4)),
--        .opent (★ -k> ★ -k> ★) ]
--        let Γ' : Ctx Term := ([ .type (#8 `@k #2 `@k #3),
--                     .type (#7 `@k #1 `@k #0),
--                     .kind ★,
--                     .kind ★,
--                     .kind ★ ] : Ctx Term) ++ Γ
--        let pτ <- infer_type Γ' (#5 `@t #3 `@t #2) -- ((#2 ~[★]~ #7) -t> ((#4 ~[★]~ #7) -t> #11 `@k #4 `@k #5))
--        -- .some pτ
--        let sτ <- infer_type Γ' #1
--        .some (pτ, sτ) -- #9 `@k #3 `@k #2
--        -- prefix_type_match Γ' pτ sτ




-- def EqFDCtx : HsCtx HsTerm := [
--   -- .inst (`∀{`★} `#3 `•k `#0 `•k `#0)
--   -- .nil,
--   .classDecl (`★ `-k> `★ `-k> `★) -- Eq a b
--     .nil
--     [([1],0), ([0], 1)] --- a ~> b, b ~> a
--     .nil

-- ]

-- #eval DsM.run (compile_ctx EqFDCtx)
-- #eval DsM.run (do
--   let Γ' <- compile_ctx EqFDCtx
--   .toDsMq (wf_ctx Γ'))


-- #eval  DsM.run (do
--   let Γ' <- compile_ctx EqFDCtx
--   let τ' <- compile Γ' ★ (`∀{`★} `#3 `•k `#0 `•k `#0)
--   let (_, iτ', _) <- mk_inst_type Γ' τ'
--   let Γ' := .insttype iτ' :: Γ'

--   .toDsMq (wf_ctx Γ')
--   )
