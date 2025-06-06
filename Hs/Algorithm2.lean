import Hs.Algorithm

@[simp]
def shift_helper_aux : Nat -> List Nat -> List Nat
| 0, acc => acc
| n + 1, acc => shift_helper_aux n (n :: acc)

@[simp]
def shift_helper : Nat -> List Nat := λ n => shift_helper_aux n []

@[simp]
def fresh_vars_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => fresh_vars_aux n (#n :: acc)

@[simp]
def fresh_vars : Nat -> List Term := λ n => fresh_vars_aux n []
@[simp]
def re_index_base := fresh_vars

#eval fresh_vars 3

theorem fresh_vars_lemma : (fresh_vars n).length == n := by sorry

@[simp]
def mk_eqs : List (Term × Term × Term) -> List Term := List.map (λ x => x.2.1 ~[x.1]~ x.2.2)

@[simp]
def mk_type_telescope : Ctx Term -> List Term -> Ctx Term := λ Γ ts =>
  List.foldl (λ Γ t_data =>
    let t := t_data.2
    let shift := t_data.1
    (.type ([S' shift] t) :: Γ)
  ) Γ (List.zip (shift_helper ts.length) ts)

@[simp]
def mk_kind_telescope : Ctx Term -> List Term -> Ctx Term := λ Γ ts =>
  List.foldl (λ Γ t_data =>
    let t := t_data.2
    let shift := t_data.1
    (.kind ([S' shift] t) :: Γ)
  ) Γ (List.zip (shift_helper ts.length) ts)

@[simp]
def mk_kind_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@k a) h args

@[simp]
def mk_kind_apps_rev : Term -> List Term -> Term
| t, [] => t
| t, .cons a args => mk_kind_apps_rev (t `@k a) args

@[simp]
def mk_ty_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@t a) h args

@[simp]
def mk_ty_apps_rev : Term -> List Term -> Term
| t, [] => t
| t, .cons a args => mk_ty_apps_rev (t `@ a) args


@[simp]
def mk_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@ a) h args

@[simp]
def mk_apps_rev : Term -> List Term -> Term
| t, [] => t
| t, .cons a args => mk_apps_rev (t `@ a) args


@[simp]
def mk_lams : Term -> Ctx Term -> Option Term
| t, [] => t
| t, .cons (.kind x) xs => do
  let t' <- (mk_lams t xs)
  .some (Λ[x] t')
| t, .cons (.type x) xs => do
  let t' <- (mk_lams t xs)
  .some (`λ[x] t')
| _, _ => .none


@[simp]
def mk_lams_rev : Term -> Ctx Term -> Option Term
| t, [] => t
| t, .cons (.kind x) xs =>
  mk_lams_rev (Λ[x] t) xs
| t, .cons (.type x) xs =>
  mk_lams_rev (`λ[x] t) xs
| _, _ => .none

-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ αs. C αs => τs -> D αs
-- and converts it to
-- ∀ βs αs. (βs ~ αs) ⇒ C αs ⇒ τs -> D βs
-- ASSUMES all type binders are in front.
-- It doesn't matter if αs have type variables, they would
-- just introduce a tyvar_new ~ tyvar_old rather than tyvar_new ~ Int
def hf_encode : Ctx Term -> (Ctx Term × Nat × List (SpineVariant × Term)) -> Option Term :=
λ Γ data => do
  let (Γ_local, d, d_τs) := data

  let d_τs_kis <- List.mapM (λ x => infer_type (Γ_local ++ Γ) x.2) d_τs

  let βs := fresh_vars d_τs.length

  let (Γ_cτs, Γ_ty) := Γ_local.partition (λ x => x.is_type)

  let eqs := mk_eqs (List.zip d_τs_kis (List.zip βs (List.map (λ x => [P' Γ_cτs.length][S' βs.length] x.snd) d_τs)))


  let ty' := [S' (eqs.length + Γ_local.length)] mk_ty_apps ([S' βs.length]#d) βs

  let Γ_cτs' := Γ_cτs.map (λ x => x.apply (S' (βs.length + eqs.length)))

  let Γ' := Γ_cτs' ++ mk_type_telescope (mk_kind_telescope Γ_ty d_τs_kis) eqs

  let ty' := ty'.from_telescope_rev Γ'

  .some ty'

def mk_inst_type : Ctx Term -> Term -> Option (Nat × Term) := λ Γ ty => do
  let (Γ_local, res_ty) := ty.to_telescope
  let (d, d_τs) <- res_ty.neutral_form
  let ty' <- hf_encode Γ (Γ_local, d, d_τs)
  .some (d, ty')


#eval (shift_helper 10).take 5


/- Caution: The ids themselves are meaningless (sort of),
  just depend on the size of the list. thats the width of the class-/
def get_openm_ids : Ctx Term -> Nat -> Option (List Nat) := λ Γ_g cls_idx =>
  if (Γ_g.is_opent cls_idx)
  then
    let ids := ((shift_helper Γ_g.length).take cls_idx).reverse
    .some ((ids.takeWhile (Γ_g.is_openm ·)).reverse)
  else .none


-- compiling declarations
def compile_ctx : HsCtx HsTerm -> Option (Ctx Term)
| [] => .some []
| .cons .empty Γ => do
  let Γ' <- compile_ctx Γ
  .some (.empty :: Γ')
| .cons (.kind k) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  .some (.kind k' :: Γ')
| .cons (.type τ) Γ => do
  let Γ' <- compile_ctx Γ
  let τ' <- compile Γ' ★ τ
  .some (.type τ' :: Γ')
| .cons (.pred τ) Γ => do
  let Γ' <- compile_ctx Γ
  let τ' <- compile Γ' ★ τ
  .some (.type τ' :: Γ')
| .cons (.term A t) Γ => do
  let Γ' <- compile_ctx Γ
  let A' <- compile Γ' ★ A
  let t' <- compile Γ' A' t
  .some (.term A' t' :: Γ')

| .cons (.datatypeDecl k ctors) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .some ((.ctor τ') ::  Γ)
    )
    (.datatype k' :: Γ') ctors

| .cons (.classDecl C scs fds oms) Γ => do
  let Γ' <- compile_ctx Γ
  let C' <- compile Γ' □ C


  -- Step 1. Add the open type
  let Γ' := .opent C' :: Γ'


  -- Step 2. Add SC constraints
  -- It amounts to producing the sc functions
  -- let scs' : Ctx Term := []
  let (args_k, _) <- Term.split_kind_arrow C'

  let ty_vars_ctx : Ctx Term := List.map (Frame.kind ·) args_k
  let ty_vars := fresh_vars args_k.length


  let Γ' <- List.foldlM ( λ Γ sc_data => do -- TODO Fix Counting

    let cls_con := sc_data.1
    let sc := sc_data.2

    let class_type := mk_kind_apps ([S' ty_vars.length]cls_con) ty_vars
    let sc' <- compile Γ ★ sc

    let sc_fun : Term := .bind2 .arrow class_type sc'
    let sc_fun := sc_fun.from_telescope_rev ty_vars_ctx

    .some (.openm sc_fun :: Γ)
    ) Γ' (List.zip (re_index_base scs.length) scs)


  -- let class_arity := ty_vars_ctx.length

  -- Step 3. Add fundeps
  let Γ' <- List.foldlM (λ Γ fd_data => do

    let cls_con := fd_data.1
    let fd := fd_data.2

    let determiners := fd.1

    let det1 := fd.2

    let det2 := args_k.length + 1

    if det1 < ty_vars_ctx.length && (List.all determiners (λ x => x < ty_vars_ctx.length))
    then do
      let ki <- (ty_vars_ctx d@ det1).get_type

      let cls_ty1 := mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars


      let ty_vars' := ty_vars.replace #det1 #det2
      -- TODO: What if the fundep is partial? also vary the irrelevant type vars
      let cls_ty2 := mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars'


      let t := cls_ty1 -t> [S](cls_ty2 -t> [S](#det1 ~[ki]~ #det2))
      let t_fun := t.from_telescope_rev (ty_vars_ctx ++ [.kind ki])

      .some (.openm t_fun :: Γ)



    else .none

  ) Γ' ((List.zip (re_index_base fds.length) fds))


  -- Step 4. Add methods
  let Γ' <- List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .some ((.openm τ') :: Γ))
      Γ' oms

  .some Γ'

| .cons (.inst ity mths) Γ => do
  let Γ'  <- compile_ctx Γ


  -- Step1: Compile instance type
  let ity' <- compile Γ' ★ ity
  let (cls_idx , ity') <- mk_inst_type Γ' ity'

  let Γ' := .insttype ity' :: Γ'

  let cls_idx := cls_idx + 1

  let openm_ids <- get_openm_ids Γ' cls_idx


  -- Step2 : Check fundeps validity
  let fds_scs_ids := openm_ids.drop openm_ids.length


  -- Step3 : compile open method
  let mths' <- List.foldlM (λ Γ x => do
    let (mth, idx) := x
    let omτ <- (Γ' d@ (cls_idx - 1)).get_type

    let (Γ_l, ret_ty) := omτ.to_telescope -- TODO maybe only peel off implicits?

    -- split Γ_l into three parts
    -- ty_args, implicit args, explicit args
    let (_, ty_args, i_args, _) <- List.foldlM (λ acc f =>
       let (Γ', x, y, z) := acc
        match f with
        | .kind _ => (f :: Γ',  x + 1, y, z)
        | .type τ => match τ.neutral_form with
           | .none => (f :: Γ',  x, y, z + 1)
           | .some (h, _) =>
             if Ctx.is_opent Γ' (x + y + z + h)
             then (f :: Γ', x, y + 1, z)
             else (f :: Γ', x, y, z + 1)
        | _ => .none
       ) (Γ', 0, 0, 0) Γ_l

    let mth' <- match mth with
    | .HsAnnotate τ mth => do
      let τ' <- compile Γ' ★ τ
      let mth' <- compile Γ' τ' mth
      let mth' := [S' (ty_args + i_args)] mth'
      let τ' := [S' (ty_args + i_args)] τ'
      let ret_ty := ret_ty.from_telescope (Γ_l.drop (ty_args + i_args))

      let η <- synth_coercion Γ τ' ret_ty
      let mth' := mth' ▹ η

      let new_vars := (fresh_vars (ty_args + i_args)).reverse
      let (ty_vars, i_vars) := new_vars.splitAt ty_args

      let guard_pat := [S' new_vars.length](mk_ty_apps #(idx) ty_vars)

      let mth' <- mk_lams (Term.guard (guard_pat) #0 (`λ[`0] ([S]mth'))) (Γ_l.take (ty_args + i_args + 1))

      .some ((Frame.inst #(cls_idx - 1) mth') :: Γ)

    | .HsVar n => .none
    | _ => .none

    )  Γ' (List.zip mths openm_ids)

  .some mths'
