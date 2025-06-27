import Hs.Algorithm
import SystemFD.Algorithm

set_option profiler true

-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ αs. assms -> D τs
-- and converts it to
-- ∀βs. ∀αs. (βs ~ αs) -> assms -> D βs
-- ASSUMES all type binders are in front in the original type
-- It doesn't matter if αs have type variables, they would
-- just introduce a tyvar_new ~ tyvar_old rather than tyvar_new ~ Int
@[simp]
def hf_encode : Ctx Term -> (Ctx Term × Nat × List (SpineVariant × Term)) -> DsM (Term × Nat) :=
λ Γ data => do
  let (Γ_l, d, d_τs) := data

  let Γ_local := Γ_l.reverse
  let d_αs_kis <- List.mapM (λ x =>
      .toDsM ("hf encode infer_kind"
            ++ Std.Format.line ++ repr (Γ_local ++ Γ) ++ Std.Format.line ++ repr x)
      (infer_kind (Γ_local ++ Γ) x.2)) d_τs

  let (Γ_αs, Γ_assms) := Γ_l.partition (λ x => x.is_kind)

  let βs := fresh_vars d_τs.length
  let βs := βs.map ([S' Γ_αs.length]·)
  let βs := βs.reverse -- the largest index to appear closest to the head (convention)


  -- all the RHS of the equality types
  let d_αs' := d_τs.map (λ x => [λ n => .re (if n < Γ_local.length
                                        then n - Γ_assms.length
                                        else n + βs.length - Γ_assms.length)] x.2)

  let eqs := Term.mk_eqs (List.zip d_αs_kis (List.zip βs d_αs'))

  let Γ_assms := Γ_assms.map (λ f => f.apply (λ n =>
              .re (if n < Γ_local.length
                   then n + βs.length
                   else n + 2*βs.length)))

  let ty' := [S' eqs.length] Term.mk_kind_apps ([S' βs.length]#d) (βs.map (λ x => [S' Γ_assms.length] x))

  let ty' := ty'.from_telescope_rev Γ_assms

  let ty' := ty'.from_telescope_rev (Term.mk_type_telescope [] eqs)

  let ty' := ty'.from_telescope_rev Γ_αs

  let ty' := ty'.from_telescope_rev (Term.mk_kind_telescope [] d_αs_kis)

  .ok (ty', d_τs.length)


@[simp]
def mk_inst_type : Ctx Term -> Term -> DsM (Nat × Term × Nat) := λ Γ ty => do
  let (Γ_local, res_ty) := ty.to_telescope
  let (d, d_τs) <- .toDsM ("mk_inst_type neutral_form" ++ Std.Format.line ++ repr res_ty) res_ty.neutral_form
  let (ty', n) <- hf_encode Γ (Γ_local, d, d_τs)
  .ok (d - Γ_local.length, ty', n)

#eval (Term.shift_helper 10).take 5

namespace Algorithm2.Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

  #guard wf_ctx Γ == .some ()
  #eval (#5 `@k #6)
  #eval DsM.run (mk_inst_type Γ (#5 `@k #6))

  #eval (∀[★] #4 `@k #0 -t> #7 `@k #1)
  #eval DsM.run (mk_inst_type Γ (∀[★] #4 `@k #0 -t> #7 `@k #1))


  def Γ0 : Ctx Term := [.datatype ★, .datatype ★, .opent (★ -k> ★ -k> ★)]
  #eval #2 `@k #0 `@k #1
  #eval DsM.run (mk_inst_type Γ0 (#2 `@k #0 `@k #1))

end Algorithm2.Test


@[simp]
def to_implicit_telescope_aux (Δ : Ctx Term) : (Ctx Term) -> Term -> Ctx Term × Term
| Γ, ∀[A] B =>
    let (Γ', r) := to_implicit_telescope_aux (.kind A :: Δ) Γ B
    (.kind A::Γ', r)
| Γ, .bind2 .arrow A B =>
    match A.neutral_form with
    | .some (h, _) =>
      if Δ.is_opent h
      then let (Γ', r) := to_implicit_telescope_aux (.type A :: Δ) Γ B
         (.type A::Γ', r)
      else (Γ, .bind2 .arrow A B)
    | .none =>
      let (Γ, r) := to_implicit_telescope_aux (.type A :: Δ) Γ B
      (.type A::Γ, r)
| Γ, t => (Γ, t)

@[simp]
def to_implicit_telescope (Δ : Ctx Term) : Term -> Ctx Term × Term := to_implicit_telescope_aux Δ []

-- compiling declarations
partial def compile_ctx : HsCtx HsTerm -> DsM (Ctx Term)
| [] => .ok []
| .cons .empty Γ => do
  let Γ' <- compile_ctx Γ
  .ok (.empty :: Γ')
| .cons (.kind k) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  .ok (.kind k' :: Γ')
| .cons (.type τ) Γ => do
  let Γ' <- compile_ctx Γ
  let τ' <- compile Γ' ★ τ
  .ok (.type τ' :: Γ')
| .cons (.term A t) Γ => do
  let Γ' <- compile_ctx Γ
  let A' <- compile Γ' ★ A
  let t' <- compile Γ' A' t
  .ok (.term A' t' :: Γ')

| .cons (.datatypeDecl k ctors) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .ok ((.ctor τ') ::  Γ)
    )
    (.datatype k' :: Γ') ctors

-- Compiling Classes
| .cons (.classDecl C scs fds oms) Γ => do
  let Γ' <- compile_ctx Γ
  let C' <- compile Γ' □ C


  -- Step 1. Add the open type
  let Γ' := .opent C' :: Γ'

  -- Step 2. Add SC constraints
  -- Produce the sc openm
  let (args_k, _) <- .toDsMq C'.split_kind_arrow

  let ty_vars_ctx : Ctx Term := List.map (Frame.kind ·) args_k
  let ty_vars := fresh_vars args_k.length


  let Γ' <- List.foldlM ( λ Γ sc_data => do

    let cls_con := sc_data.1 -- the current class constructor

    let sc := sc_data.2 -- Superclass type
    let (sc_tycon, ty_args) <- .toDsMq sc.neutral_form -- Split it into ctor and ty_args

    let class_type := Term.mk_kind_apps_rev ([S' ty_vars.length]cls_con) ty_vars.reverse

    let sc' <- compile (ty_vars_ctx ++ Γ) ★ sc

    let sc_fun : Term :=  class_type -t> ([S]sc') -- [S] becuase -t> is binder
    let sc_fun := sc_fun.from_telescope_rev ty_vars_ctx

    .ok (.openm sc_fun :: Γ)
    ) Γ' (List.zip (re_index_base scs.length) scs)


  -- let class_arity := ty_vars_ctx.length

  -- Step 3. Add fundeps open methods
  let Γ' <- List.foldlM (λ Γ fd_data => do

    let cls_con := fd_data.1
    let fd := fd_data.2

    let determiners := fd.1

    let det1 := fd.2

    let det2 := 0 -- the new determinant is always the innermost

    if det1 < ty_vars_ctx.length && (List.all determiners (λ x => x < ty_vars_ctx.length))
       -- check that the fun dep is well scoped
    then do
      let ki <- .toDsMq (ty_vars_ctx d@ det1).get_type
      let ret_ty := (#(det1 + 1) ~[ki]~ #det2)


      let ty_vars_inner := ((ty_vars.map ([S]·)).modify det1 (λ _ => #det2)).reverse
      let cls_ty_inner := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars_inner

      let ret_ty := cls_ty_inner -t> [S] ret_ty

      let ty_vars_outer := (ty_vars.map ([S]·)).reverse
      let cls_ty_outer := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars_outer

      let ret_ty := cls_ty_outer -t> [S] ret_ty
      -- -- TODO: What if the fundep is partial? also vary the irrelevant type vars?

      let t_fun := ret_ty.from_telescope_rev (.kind ki :: ty_vars_ctx)

      .ok (.openm t_fun :: Γ)


    else .error ("fundeps: " ++ repr Γ ++ repr fd_data)

  ) Γ' ((List.zip (re_index_base fds.length) fds))


  -- Step 4. Add methods
  let Γ' <- List.foldlM
    (λ Γ om_data => do
      let (idx, τ) := om_data
      let τ' <- compile Γ ★ τ
      let (Γ_l, ret_ty) := τ'.to_telescope
      let (Γ_tyvars, Γ_rest) := Γ_l.partition (λ x => x.is_kind)
      let class_ty := Term.mk_kind_apps (#(scs.length + fds.length + Γ_tyvars.length + idx))
                       (ty_vars.reverse.map ([S' (Γ_tyvars.length - ty_vars.length)] ·))
      let Γ_rest := Γ_rest.map (λ f => f.apply S)
      let Γ_l := Γ_tyvars ++ (.type class_ty :: Γ_rest)
      let ret_ty := [S] ret_ty

      let τ' := ret_ty.from_telescope Γ_l

      .ok ((.openm τ') :: Γ))
      Γ' (List.zip (Term.shift_helper oms.length) oms)

  .ok Γ'

-- Compile Instances
| .cons (.inst ity mths) Γ => do
  let Γ'  <- compile_ctx Γ

  -- Step1: Compile instance type
  -- ity is of the form C τs ⇒ D τs
  let ity_orig' <- compile Γ' ★ ity
  let (cls_idx , ity', β_count) <- mk_inst_type Γ' ity_orig'

  let Γ' := .insttype ity' :: Γ'

  let cls_idx := cls_idx + 1 -- account for insttype at head
  -- let instty_idx := 0

  let openm_ids <- get_openm_ids Γ' cls_idx
  -- open_ids are class omτs ++ sc omτ ++ fundeps omτ


  let (fd_ids, openm_ids) := openm_ids.partition (λ x =>
      let f := Γ' d@ x
      if f.is_openm then
        match f.get_type with
        | .some τ =>
          let (_, ret_ty) := Term.to_telescope τ;
          Option.isSome (is_eq ret_ty)
        | .none => false
      else false )


  let (sc_ids, openm_ids) := openm_ids.partition (λ x =>
       let f := Γ' d@ x
       if f.is_openm then
         match f.get_type with
         | .some τ =>
           let (tele, ret_ty) := Term.to_telescope τ;
           match ret_ty.neutral_form with
           | .none => true
           | .some (h, _) => (tele ++ Γ').is_opent h
         | .none => false
       else false)

  -- Step1 : Check fundeps validity

  -- Step2 : Add fundeps instances
  let Γ' <- List.foldlM (λ Γ fd_id => do

    let omτ <- .toDsM "get fd type"
               (Γ d@ (cls_idx - 1)).get_type
    let (Γ_l, ret_ty) := omτ.to_telescope

    -- fd openmethod is of the form: i.e. the varied tyvar is inner most ty var
    -- ∀αs t' F αs t -> F αs t' -> (t ~ t')
    let (Γ_tyvars, Γ_insts) := Γ_l.partition (λ x => x.is_kind)
    if Γ_insts.length == 2
    then
      match is_eq ret_ty with
      | .none => .error ("fd om broken" ++ repr omτ)
      | .some (_, #A, #B) =>
        let new_vars := (fresh_vars Γ_l.length).reverse
        let (ty_vars, inst_vars) := new_vars.splitAt Γ_tyvars.length

        let ty_vars_outer := ty_vars.take (ty_vars.length - 1) -- drop the last elem of the list
        -- let temp := (ty_vars.take (ty_vars.length - 1)).splitAt (ty_vars.length - 1) -- drop the last elem of the list

        let ty_vars_inner := ty_vars.take (ty_vars.length - 1)  -- drop the last elem of the list and put it up front
        -- let temp := ty_vars_inner.splitAt (ty_vars_inner.length - 1)
        -- let ty_vars_inner := temp.2 ++ temp.1
        -- let target_idxA := A - 2
        -- let target_idxB := B - 2

        let inst_1 : Frame Term <- .toDsM "inst 1 failed" (Γ_insts[0]?)
        let inst_1 <- .toDsMq inst_1.get_type

        let inst_2 : Frame Term <- .toDsM "inst 2 failed" (Γ_insts[1]?)
        let inst_2 <- .toDsMq inst_2.get_type
        let inst_2 := [P] inst_2 -- rebase it relative to Γ_tyvars

        let (h_1, τs_1) <- .toDsM ("inst_1 neutral form" ++ repr inst_1)
                           inst_1.neutral_form
        let (h_2, τs_2) <- .toDsM ("inst_2 neutral form" ++ repr inst_2)
                           inst_2.neutral_form

        -- find the index that differs in τs_1 and τs_2
        let idx_diff : List Nat :=
            ((List.zip (Term.shift_helper τs_1.length) (List.zip τs_1 τs_2)).foldl
              (λ acc x =>
                    if acc.isEmpty
                    then let (n, (t1, t2)) := x
                       if t1 == t2 then acc else [n]
                                   else acc) [])
        match idx_diff[0]? with
        | .none => .error ("index diff" ++ repr τs_1 ++ repr τs_2)
        | .some ι =>

          -- build the term from inside out
        let ty_vars_inner := ty_vars_inner.modify ι (λ _ => #inst_vars.length) -- set the determinant to the correct idx
        let instτ : Term <- .toDsM "fd gettype" ((Γ d@ fd_id).get_type)
        let instτ := ([S' Γ_l.length]instτ) -- shift to be relative to Γ_l ++ Γ


        -- TODO : find a fix for general case where some variables are locally bound in the instance
        -- constraint
        let outer_pat_tyvars := ty_vars_outer
        let guard_pat_outer := Term.mk_ty_apps #(fd_id + Γ_l.length) outer_pat_tyvars
        let inst_ty_outer <- .toDsM "instantate instτ outer" (instantiate_types instτ outer_pat_tyvars)
        let (Γ_instτ_outer, _) := inst_ty_outer.to_telescope

        let inner_pat_tyvars := ty_vars_inner.map ([S' Γ_instτ_outer.length] ·)
        let guard_pat_inner := Term.mk_ty_apps #(fd_id + Γ_l.length + Γ_instτ_outer.length) inner_pat_tyvars
        let inst_ty_inner <- .toDsM "instantiate instτ inner"
                             (instantiate_types ([S' Γ_instτ_outer.length]instτ) inner_pat_tyvars)
        let (Γ_instτ_inner, _) := inst_ty_inner.to_telescope

        let Γ_instτ_inner := Γ_instτ_inner.reverse
        let Γ_instτ_outer := Γ_instτ_outer.reverse
        let Γ_l := Γ_l.reverse

        let ctx_l := (Γ_instτ_inner ++ Γ_instτ_outer ++ Γ_l ++ Γ)
        let τ := [S' (Γ_instτ_inner.length + Γ_instτ_outer.length)]ret_ty
        let η <- .toDsM ("fd synth_term"
                     ++ Std.Format.line ++ "τ: " ++ repr τ
                     ++ Std.Format.line ++ "ctx Γ: " ++ repr ctx_l
                     ++ Std.Format.line ++ "Γ_inner: " ++ repr Γ_instτ_inner
                     ++ Std.Format.line ++ "Γ_outer: " ++ repr Γ_instτ_outer
                     ++ Std.Format.line ++ "Γ_l: " ++ repr Γ_l
                     ++ Std.Format.line ++ "Γ: " ++ repr Γ_l
                     ++ Std.Format.line ++ "β_count: " ++ repr β_count
                     ++ Std.Format.line ++ "vars: " ++ repr ty_vars ++ repr inst_vars

                     ++ Std.Format.line ++ "ty_vars_inner: " ++ repr ty_vars_inner
                     ++ Std.Format.line ++ "guard_pat_inner: " ++ repr guard_pat_inner ++ " : " ++ repr inst_ty_inner

                     ++ Std.Format.line ++ "ty_vars_outer: " ++ repr ty_vars_outer
                     ++ Std.Format.line ++ "guard_pat_outer: " ++ repr guard_pat_outer ++ " : " ++ repr inst_ty_outer
                     ++ Std.Format.line ++ "τs_1 τs_2 ι " ++ repr τs_1 ++ repr τs_2 ++ repr ι
                     ) (synth_term ctx_l τ)

          -- let η := ([S' (Γ_instτ_inner ++ Γ_instτ_outer).length]ret_ty)

        let iterm <- .toDsM ("fd mk_lams inner pat") (η.mk_lams_rev Γ_instτ_inner)
        let iterm := .guard guard_pat_inner (#Γ_instτ_outer.length) iterm

        let iterm <- .toDsM ("fd mk_lams outer pat")
                         (Term.mk_lams_rev iterm Γ_instτ_outer)

        let iterm := .guard guard_pat_outer #1 iterm

        let iterm <- .toDsM ("fd mk_lams" ++ repr Γ_insts)
                            (Term.mk_lams_rev iterm Γ_l)

        let Γ_new := .inst #(cls_idx - 1) iterm :: Γ
        .ok Γ_new
      | _ => .error ("fd ret eq non variables" ++ repr omτ)

    else .error ("fd inst failure" ++ repr omτ)

  ) Γ' (Term.shift_helper fd_ids.length)


  -- Step 4: Compile superclass insts
  let Γ' <- List.foldlM (λ Γ sc_id => do

    let omτ <- .toDsM "sc get_type omτ" (Γ d@ (cls_idx - (1 + fd_ids.length))).get_type
    let (Γ_l, ret_ty) := omτ.to_telescope

    let (ty_args_ctx, _) := List.partition (λ x => Frame.is_kind x) Γ_l
    let new_vars := fresh_vars Γ_l.length
    let ty_vars : List Term := new_vars.reverse.take (ty_args_ctx.length)

    let g_pat := Term.mk_ty_apps #(sc_id + fd_ids.length + Γ_l.length) ty_vars
    let g_pat_ty <- .toDsM "sc get_type g_pat_ty" ((Γ_l ++ Γ) d@ (sc_id + fd_ids.length + Γ_l.length)).get_type
    let g_pat_ty <- .toDsM "sc inst type g_pat_ty" (instantiate_types g_pat_ty ty_vars)
    let (eqs, _) := g_pat_ty.to_telescope

    let t' <- .toDsM ("synth_sc_inst")
              (synth_superclass_inst (Γ_l  ++ Γ) ty_vars (([S' eqs.length] ret_ty).from_telescope eqs))
    let sc_fun <- .toDsM "sc insts mk_lams" (Term.mk_lams (Term.guard g_pat #0 t') Γ_l)
    let new_Γ := .inst #(cls_idx - (1 + fd_ids.length)) sc_fun :: Γ
    .ok new_Γ

  ) Γ' (Term.shift_helper sc_ids.length)

  let cls_idx := cls_idx + sc_ids.length

  -- Step3 : compile open method
  let Γ' <- if  mths.length == openm_ids.length -- insist on all methods being implemented
  then

    List.foldlM (λ Γ x => do
      let (mth, idx) := x

      let instty <- .toDsM "om instty" (Γ d@ (idx + sc_ids.length + fd_ids.length)).get_type

      let (Γ_inst, _) := instty.to_telescope
      let (Γ_tyvars, Γ_rest) := Γ_inst.partition (λ x => x.is_kind)
      let (Γ_tyvars_βs, Γ_tyvars_αs) := Γ_tyvars.splitAt β_count
      let (Γ_eqs, Γ_assms) := Γ_rest.partition (λ x =>
        match x with
        | .type x => (Option.isSome (is_eq x))
        | _ => false
        )

      let new_vars := (fresh_vars Γ_inst.length).reverse

      let (ty_vars, rest_new_vars) := new_vars.splitAt Γ_tyvars.length
      let (vars_eq, vars_assms) := rest_new_vars.splitAt Γ_eqs.length

      let (ty_vars_βs, ty_vars_αs) := ty_vars.splitAt β_count

      let Γ_local := Γ_inst.reverse

      /-  insttype is of the form ∀βs ∀αs. (βs ~ αs) -> C αs -> D βs
                   where C and D are opent's
          the openm type is of the form ∀βs A βs -> τs -> ret_τ
                   where A is an opent
          the inst binding type is of the form ∀δs B δs -> τs' -> ret_τ'

          the generated instance looks like
                  Λβs. λD βs
                    Guard #inst [βs] <- #0
                      Λαs. λ(βs ~ αs) λ C αs
                           mth[βs] γs ▹ η

                  where γ : B βs
                        η : ((τs' -> ret_τ)[δs ↦ βs]) ~ τs -> ret_τ
                  and γ and η are synthesized
      -/


      let omτ <- .toDsM "omτ get_type2" (Γ d@ (cls_idx - (1 + sc_ids.length + fd_ids.length))).get_type
      let omτ := [S' (Γ_local.length)] omτ
      let inst_omτ <- .toDsM ("instantate omτ"
                             ++ Std.Format.line ++ repr omτ
                             ++ Std.Format.line ++ repr ty_vars_βs
                             )
                             (instantiate_types omτ ty_vars_βs)
      let (omτ_assms, omτ_ret_ty) := to_implicit_telescope (Γ_local ++ Γ) inst_omτ
      -- TODO: make sure all omτ_assms (sans current instance constraints) are satisfied with the assumptions we have


      let (mth_τ', mth') <- match mth with
      | .HsAnnotate τ mth  => do
        let τ' <- compile Γ ★ τ
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | .HsVar n => do
        let τ' <- .toDsMq (Γ d@ n).get_type
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | _ => .error ("unsupported method decl: " ++ repr mth)

      let mth_τ' := [S' Γ_local.length] mth_τ'
      let mth_τ' <- .toDsM "instantate mth_τ"
                    (instantiate_types mth_τ' ty_vars_αs)

      let (Γ_mthτ'_θ, ret_mth_τ') := to_implicit_telescope (Γ_local ++ Γ) mth_τ'

      let mth' := [S' Γ_local.length] mth'


      let ctx_l := Γ_local ++ Γ

      -- TODO: omτ may give us more assumptions to be added into the context
      -- let omτ_assms' <- omτ_assms.tail.mapM (λ x => .toDsMq (x.get_type))
      -- let (_, inst_mth_assms) <- List.foldlM (λ acc τ => do
      --     let (ctx_l', ts) := acc
      --     let t <- DsM.toDsM ("") (synth_term ctx_l' τ)
      --     .ok ((Frame.empty :: ctx_l'), t :: ts)
      --     ) (ctx_l, []) omτ_assms'

      let mthτ'_θ <- Γ_mthτ'_θ.mapM (λ x => .toDsMq x.get_type)
      let (inst_mth_assms) <- List.foldlM (λ ts (idx, θτ) => do
          let θτ := [P' idx]θτ -- need all the implicit pred evidences relative to ctx_l
          let t <- .toDsM ("mth_θ synth_term"
                    ++ Std.Format.line ++ "θτ: " ++ repr θτ
                    ++ Std.Format.line ++ "ctx Γ: " ++ repr ctx_l
                    ++ Std.Format.line ++ "ts: " ++ repr ts
                   )
                   (synth_term ctx_l θτ)
          .ok (t :: ts)
          ) [] (List.zip (Term.shift_helper mthτ'_θ.length) mthτ'_θ)

      let mth' := Term.mk_ty_apps mth' ty_vars_αs

      let mth' := mth'.mk_apps inst_mth_assms

      -- TODO : apply mth' to the omτ assumptions?

      let Aτ := [P' Γ_mthτ'_θ.length]ret_mth_τ' -- rebase to ctx_l
      let Bτ := [P]omτ_ret_ty -- we take away the first omτ_assms as its the implicitly introduced class constraint
      let η <- .toDsM ("synth_coercion mth"
                        ++ Std.Format.line ++ "insttype: " ++ repr instty
                        ++ Std.Format.line ++ "omτ_assms: " ++ repr omτ_assms

                        ++ Std.Format.line ++ "Γ_inst_assms: " ++ repr Γ_assms ++ repr vars_assms
                        ++ Std.Format.line ++ "Γ_inst_eqs" ++ repr Γ_eqs ++ repr vars_eq
                        ++ Std.Format.line ++ "Γ_inst_αs: " ++ repr (Γ_tyvars.drop β_count)  ++ repr ty_vars_αs
                        ++ Std.Format.line ++ "Γ_inst_βs: " ++ repr (Γ_tyvars.take β_count) ++ repr ty_vars_βs
                        ++ Std.Format.line ++ "Γ: " ++ repr Γ

                        ++ Std.Format.line ++ "ctx Γ: " ++ repr ctx_l
                        ++ Std.Format.line  ++ "Eq: " ++ repr (Aτ ~[★]~ Bτ)
                        ++ Std.Format.line ++ "mth_τ': " ++ repr mth_τ'
                        ++ Std.Format.line ++ "omτ: " ++ repr omτ ++ " inst: " ++ repr inst_omτ
                        ++ Std.Format.line ++ "mth': " ++ repr mth'
                        ++ Std.Format.line ++ "cls_idx: " ++ repr cls_idx
                      )
                      (synth_coercion ctx_l Aτ Bτ)

      let mth' := mth' ▹ η

      -- let Γ_assms' := (Γ_assms.map (λ f => f.apply S)).reverse
      let mth' <- .toDsM ("Term.mk_lams Γ_assms" ++ repr mth' ++ Std.Format.line ++ repr Γ_assms)
                         (Term.mk_lams mth' Γ_assms)

      -- let Γ_eqs' := (Γ_eqs.map (λ f => f.apply S)).reverse
      let mth' <- .toDsM ("Term.mk_lams Γ_eqs" ++ repr mth' ++ Std.Format.line ++ repr Γ_eqs)
                         (Term.mk_lams mth' Γ_eqs.reverse)

      let mth' <- .toDsM ("Term.mk_lams Γ_eqs" ++ repr mth' ++ Std.Format.line ++ repr Γ_eqs)
                         (Term.mk_lams mth' Γ_tyvars_αs.reverse)

      let mth' := [S] mth' -- account for instance constraint

      let g_pat := Term.mk_ty_apps #(idx + sc_ids.length + fd_ids.length + ty_vars_βs.length + 1)
                           (ty_vars_βs.map ([P' (Γ_assms.length + ty_vars_αs.length)] ·))

      let mth' := Term.guard g_pat #0 mth'

      let cls_ty := (#(cls_idx + ty_vars_βs.length + idx)).mk_kind_apps
                           (ty_vars_βs.map ([P' (Γ_assms.length + ty_vars_αs.length + Γ_eqs.length)]· ))
      let mth' <- .toDsM ("Term.mk_lams" ++ repr mth'
                         ++ Std.Format.line ++ repr (.type cls_ty :: Γ_tyvars_βs).reverse)
                         (Term.mk_lams mth' (.type cls_ty :: Γ_tyvars_βs).reverse)

      let new_Γ := ((Frame.inst #(cls_idx - (1 + sc_ids.length + fd_ids.length)) mth') :: Γ)

      .ok new_Γ

    )  Γ' (List.zip mths (Term.shift_helper openm_ids.length))
  else .error ("Not all methods implemented" ++ repr mths ++ Std.Format.line ++ repr openm_ids)

  .ok Γ'

-- #eval instantiate_type (∀[★] ((#0 ~[★]~ #4) -t> #7 `@k #1)) #100
-- #eval [0,1].splitAt 1
-- #eval [0,1,2,3].take 3

-- #eval do
--   let (h, sp) <- (#0 `@t #1 `@t #2).neutral_form
--   let sp' : List Term := sp.map (λ x =>
--           let (_ , x') : (SpineVariant × Term) := x
--           x')
--   .some (Term.mk_ty_apps #h sp')
