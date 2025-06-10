import Hs.HsTerm
import Hs.Algorithm2
import SystemFD.Algorithm
import SystemFD.Term

import Hs.Examples.Datatypes
import Hs.Examples.Classes

-- def BoolCtx : HsCtx HsTerm :=
--   [ .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
--                      , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
--                      ]
--   ]

-- class Eq a where
--   == : a -> a -> Bool
--   =/= : a -> a -> Bool

-- def EqCFrame : HsFrame HsTerm :=
--   HsFrame.classDecl (`★ `-k> `★)
--          .nil
--          .nil
--          [ `∀{`★} (`#1 `•k `#0) ⇒ `#1 → `#2 → `#7    -- TODO: make type class predicate implicit?
--          , `∀{`★} (`#2 `•k `#0) ⇒ `#1 → `#2 → `#8 ]

-- def EqCtx : HsCtx HsTerm :=
--   EqCFrame :: BoolCtx


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
    [ `∀{`★} (`#2 `•k `#0) ⇒ (`#1 → `#2 → `#14)
    ]


def OrdBool : HsFrame HsTerm :=
  HsFrame.inst
  (`#2 `•k `#11)
  [ .HsAnnotate (`#12 → `#13 → `#14) (λ̈[`#12] λ̈[`#13] `#13)

  ]

def supCtx := -- OrdBool ::
              OrdC ::
              EqBoolI ::
              EqCtx

#eval println! "OrdBool, Ord, EqBool, Bool"
#eval supCtx
#eval! compile_ctx supCtx
#eval! do let ctx <- compile_ctx supCtx
          wf_ctx ctx


#eval! do let ctx <- compile_ctx (EqBoolI :: EqCtx)
          let ctx := Frame.opent (★ -k> ★) :: ctx

          let args_k : List Term := .cons ★ []

          let ty_vars_ctx : Ctx Term := List.map (Frame.kind ·) args_k
          let ty_vars := fresh_vars args_k.length


          let cls_con : Term := #0 -- sc_data.1
          let sc := `#7 `•k `#0 -- sc_data.2

          let class_type := mk_kind_apps_rev ([S' ty_vars.length] cls_con) ty_vars
          -- .some class_type
          let sc' <- compile (ty_vars_ctx ++ ctx) ★ sc
          .some sc'
          -- let sc_fun : Term :=  class_type -t> ([S]sc') -- [S] becuase -t> is binder
          -- let sc_fun := sc_fun.from_telescope ty_vars_ctx

          -- .some (.openm sc_fun :: Γ)



          -- .some ctx

          -- let openm_ids <- get_openm_ids ctx 5
          -- let (sc_ids, openm_ids) := openm_ids.partition (λ x =>
          --     match (ctx d@ x).get_type with
          --     | .some τ =>
          --       let (tele, ret_ty) := Term.to_telescope τ;
          --       match ret_ty.neutral_form with
          --       | .none => true
          --       | .some (h, _) => (tele ++ ctx).is_opent h
          --     | .none => false)

          -- let (fd_ids, openm_ids) := openm_ids.partition (λ x =>
          --     match (ctx d@ x).get_type with
          --     | .some τ =>
          --       let (_, ret_ty) := Term.to_telescope τ;
          --       Option.isSome (is_eq ret_ty)
          --     | .none => false)
          -- .some (fd_ids, sc_ids, openm_ids)

          -- let omτ <- (ctx d@ (3 - 1 + sc_ids.length + fd_ids.length)).get_type
          -- -- .some omτ
          -- let τ : HsTerm := (`#6 → `#7 → `#8)
          -- let τ' <- compile ctx ★ τ
          -- let mth := λ̈[`#6] λ̈[`#7] `#7
          -- let mth' <- compile ctx τ' mth
          -- let (Γ_l, ret_ty) := to_implicit_telescope ctx omτ

          -- let (ty_args, _) := Γ_l.partition (λ x => Frame.is_kind x)

          -- let τ' := [S' Γ_l.length] τ'
          -- let new_vars := (fresh_vars Γ_l.length).reverse  -- [#1, #0]
          -- let (ty_vars, _) := new_vars.splitAt ty_args.length -- [#1], [#0]

          -- let g_pat := (mk_ty_apps #(3 - 1 + sc_ids.length + fd_ids.length + Γ_l.length) ty_vars.reverse)
          -- -- .some g_pat
          -- let instty <- ((Γ_l ++ ctx) d@ (0 + sc_ids.length + fd_ids.length + Γ_l.length)).get_type
          -- let instty <- instantiate_types instty ty_vars
          -- -- .some instty
          -- let (tele, _ ) := instty.to_telescope
          -- -- .some tele
          -- let inst_ty_coercions := tele.filter (λ (x : Frame Term) =>
          --        match x with
          --        | .type τ => Option.isSome (is_eq τ)
          --        | _ => false)

          -- -- .some inst_ty_coercions
          -- let η <- synth_coercion (inst_ty_coercions ++ Γ_l ++ ctx)
          --            ([S' (inst_ty_coercions.length)]τ')
          --            ([S' (inst_ty_coercions.length)]ret_ty)

          -- let mth' := [S' (inst_ty_coercions.length + Γ_l.length)] mth'
          -- let mth' <- mk_lams (mth' ▹ η)
          --                 inst_ty_coercions

          -- let mth' <- mk_lams (Term.guard g_pat #0 mth') Γ_l

          -- .some (Frame.inst #(3 - (1 + sc_ids.length + fd_ids.length)) mth' :: ctx)
