import Hs.Algorithm
import SystemFD.Algorithm

set_option profiler true


@[simp]
def fresh_vars_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => fresh_vars_aux n (#n :: acc)

@[simp]
def fresh_vars : Nat -> List Term := λ n => fresh_vars_aux n []
@[simp]
def re_index_base := fresh_vars

#eval fresh_vars 3

-- theorem fresh_vars_aux_lemm : (fresh_vars_aux n l).length = l.length + n := by
-- sorry
-- theorem fresh_vars_lemma : (fresh_vars n).length == n := by
-- sorry

-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ αs. C αs => τs -> D αs
-- and converts it to
-- ∀ βs αs. (βs ~ αs) ⇒ C αs ⇒ τs -> D βs
-- ASSUMES all type binders are in front.
-- It doesn't matter if αs have type variables, they would
-- just introduce a tyvar_new ~ tyvar_old rather than tyvar_new ~ Int
@[simp]
def hf_encode : Ctx Term -> (Ctx Term × Nat × List (SpineVariant × Term)) -> DsM Term :=
λ Γ data => do
  let (Γ_local, d, d_τs) := data

  let d_τs_kis <- List.mapM (λ x => .toDsM ("hf encode infer_type" ++ repr x)
                  (infer_type (Γ_local ++ Γ) x.2)) d_τs

  let βs := fresh_vars d_τs.length

  let (Γ_cτs, Γ_ty) := Γ_local.partition (λ x => x.is_type)

  let eqs := Term.mk_eqs (List.zip d_τs_kis (List.zip βs (List.map (λ x => [P' Γ_cτs.length][S' βs.length] x.snd) d_τs)))


  let ty' := [S' (eqs.length + Γ_local.length)] Term.mk_kind_apps ([S' βs.length]#d) βs

  let Γ_cτs' := Γ_cτs.map (λ x => x.apply (S' (βs.length + eqs.length)))

  let Γ' := Γ_cτs' ++ Term.mk_type_telescope (Term.mk_kind_telescope Γ_ty d_τs_kis) eqs

  let ty' := ty'.from_telescope_rev Γ'

  .ok ty'

@[simp]
def mk_inst_type : Ctx Term -> Term -> DsM (Nat × Term) := λ Γ ty => do
  let (Γ_local, res_ty) := ty.to_telescope
  let (d, d_τs) <- .toDsMq res_ty.neutral_form
  let ty' <- hf_encode Γ (Γ_local, d, d_τs)
  .ok (d, ty')


#eval (Term.shift_helper 10).take 5


/- Caution: The ids themselves are meaningless (sort of),
  just depend on the size of the list. thats the width of the class-/
@[simp]
def get_openm_ids : Ctx Term -> Nat -> DsM (List Nat) := λ Γ_g cls_idx =>
  if (Γ_g.is_opent cls_idx)
  then
    let ids := ((Term.shift_helper Γ_g.length).take cls_idx).reverse
    .ok ((ids.takeWhile (Γ_g.is_openm ·)).reverse)
  else .error ("get_open_ids" ++ (repr Γ_g) ++ repr cls_idx)



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
unsafe def compile_ctx : HsCtx HsTerm -> DsM (Ctx Term)
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

    let class_type := Term.mk_kind_apps_rev ([S' ty_vars.length]cls_con) ty_vars

    let sc' <- compile (ty_vars_ctx ++ Γ) ★ sc

    let sc_fun : Term :=  class_type -t> ([S]sc') -- [S] becuase -t> is binder
    let sc_fun := sc_fun.from_telescope ty_vars_ctx

    .ok (.openm sc_fun :: Γ)
    ) Γ' (List.zip (re_index_base scs.length) scs)


  -- let class_arity := ty_vars_ctx.length

  -- Step 3. Add fundeps
  let Γ' <- List.foldlM (λ Γ fd_data => do

    let cls_con := fd_data.1
    let fd := fd_data.2

    let determiners := fd.1

    let det1 := fd.2

    let det2 := args_k.length

    if det1 < ty_vars_ctx.length && (List.all determiners (λ x => x < ty_vars_ctx.length))
    then do
      let ki <- .toDsMq (ty_vars_ctx d@ det1).get_type

      let cls_ty1 := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars.reverse


      let ty_vars' := ty_vars.replace #det1 #det2
      -- TODO: What if the fundep is partial? also vary the irrelevant type vars
      let cls_ty2 := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars'.reverse


      let t := cls_ty1 -t> [S](cls_ty2 -t> [S](#det1 ~[ki]~ #det2))
      let t_fun := t.from_telescope_rev (ty_vars_ctx ++ [.kind ki])

      .ok (.openm t_fun :: Γ)



    else .error ("fundeps: " ++ repr Γ ++ repr fd_data)

  ) Γ' ((List.zip (re_index_base fds.length) fds))


  -- Step 4. Add methods
  let Γ' <- List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .ok ((.openm τ') :: Γ))
      Γ' oms

  .ok Γ'

-- Compile Instances
| .cons (.inst ity mths) Γ => do
  let Γ'  <- compile_ctx Γ

  -- Step1: Compile instance type
  let ity' <- compile Γ' ★ ity
  let (cls_idx , ity') <- mk_inst_type Γ' ity'

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

    -- let omτ <- (Γ d@ (cls_idx - 1)).get_type
    -- let (Γ_l, ret_ty) := omτ.to_telescope


    -- let sc_fun := ret_ty
    -- let Γ_new := .inst #(cls_idx - 1) sc_fun :: Γ
    -- .ok Γ_new
    .ok Γ
  ) Γ' (Term.shift_helper fd_ids.length)


  -- Step 4: Compile superclass insts
  let Γ' <- List.foldlM (λ Γ sc_id => do

    let omτ <- .toDsMq (Γ d@ (cls_idx - (1 + fd_ids.length))).get_type
    let (Γ_l, ret_ty) := omτ.to_telescope

    let (ty_args_ctx, _) := List.partition (λ x => Frame.is_kind x) Γ_l
    let new_vars := fresh_vars Γ_l.length
    let ty_vars : List Term := new_vars.reverse.take (ty_args_ctx.length)

    let g_pat := Term.mk_ty_apps #(sc_id + fd_ids.length + Γ_l.length) ty_vars
    let g_pat_ty <- .toDsMq ((Γ_l ++ Γ) d@ (sc_id + fd_ids.length + Γ_l.length)).get_type
    let g_pat_ty <- .toDsMq (instantiate_types g_pat_ty ty_vars)
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
      let omτ <- .toDsMq (Γ d@ (cls_idx - (1 + sc_ids.length + fd_ids.length))).get_type

      let (Γ_l, ret_ty) := to_implicit_telescope Γ omτ

    -- split Γ_l into two parts
    -- ty_args, implicit args
      let (ty_args, _) := List.partition (λ x => x.is_kind) Γ_l
      let (τ', mth') <- match mth with
      | .HsAnnotate τ mth  => do
        let τ' <- compile Γ ★ τ
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | .HsVar n => do
        let τ' <- .toDsMq (Γ d@ n).get_type
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | _ => .error ("unsupported method decl: " ++ repr mth)


      let τ' := [S' Γ_l.length] τ'
      let new_vars := (fresh_vars Γ_l.length).reverse  -- [#1, #0]
      let (ty_vars, _) := new_vars.splitAt ty_args.length -- [#1], [#0]

      let g_pat := (Term.mk_ty_apps #(idx + sc_ids.length + fd_ids.length + Γ_l.length) ty_vars)

      let instty <- .toDsMq ((Γ_l ++ Γ) d@ (idx + sc_ids.length + fd_ids.length + Γ_l.length)).get_type
      let instty <- .toDsM ("instantiate" ++ repr instty ++ repr ty_vars) (instantiate_types instty ty_vars)

      let (tele, _ ) := instty.to_telescope
      let inst_ty_coercions := tele.filter (λ x =>
        match x with
        | .type τ => Option.isSome (is_eq τ)
        | _ => false)

      let ctx_l := (inst_ty_coercions ++ Γ_l ++ Γ)
      let Aτ := [S' (inst_ty_coercions.length)]τ'
      let Bτ := ([S' (inst_ty_coercions.length)]ret_ty)
      let η <- .toDsM ("synth_coercion" ++ repr ctx_l ++ Std.Format.line ++ repr Aτ ++ Std.Format.line ++ repr Bτ)
                      (synth_coercion ctx_l Aτ Bτ)



      let mth' := [S' (inst_ty_coercions.length + Γ_l.length)] mth'
      let mth' <- .toDsM ("Term.mk_lams" ++ repr (mth' ▹ η) ++ Std.Format.line ++ repr inst_ty_coercions)
                          (Term.mk_lams (mth' ▹ η) inst_ty_coercions)

      let mth' <- .toDsM ("Term.mk_lams" ++ repr (Term.guard g_pat #0 mth') ++ Std.Format.line ++ repr Γ_l)
                         (Term.mk_lams (Term.guard g_pat #0 mth') Γ_l)

      let new_Γ := ((Frame.inst #(cls_idx - (1 + sc_ids.length + fd_ids.length)) mth') :: Γ)
      -- let cls_idx := cls_idx + 1
      .ok new_Γ

    )  Γ' (List.zip mths (Term.shift_helper openm_ids.length))
  else .error ("Not all methods implemented don't match" ++ repr mths ++ Std.Format.line ++ repr openm_ids)

  .ok Γ'

-- #eval instantiate_type (∀[★] ((#0 ~[★]~ #4) -t> #7 `@k #1)) #100
-- #eval [0,1].splitAt 1
-- #eval [0,1,2,3].take 3
