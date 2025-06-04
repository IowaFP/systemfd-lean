import Hs.Algorithm

@[simp]
def shift_helper_aux : Nat -> List Nat -> List Nat
| 0, acc => acc
| n + 1, acc => shift_helper_aux n (n :: acc)

@[simp]
def shift_helper : Nat -> List Nat := λ n => shift_helper_aux n []

@[simp]
def new_binders_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => new_binders_aux n (#n :: acc)

@[simp]
def new_binders : Nat -> List Term := λ n => new_binders_aux n []
@[simp]
def re_index_base := new_binders

#eval new_binders 3

theorem new_binders_lemma : (new_binders n).length == n := by sorry

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
def mk_ty_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@t a) h args

@[simp]
def mk_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@ a) h args


-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ αs. C αs => τs -> D αs
-- and converts it to
-- ∀ βs αs. (βs ~ αs) ⇒ C αs ⇒ τs -> D βs
-- ASSUMES all type binders are upfront.
-- It doesn't matter if αs have type variables, they would
-- just introduce a tyvar_new ~ tyvar_old rather than tyvar_new ~ Int
def hf_encode : Ctx Term -> Term -> Option Term := λ Γ ty => do
  let (Γ_local, res_ty) := ty.to_telescope
  let (d, d_τs) <- res_ty.neutral_form

  let d_τs_kis <- List.mapM (λ x => infer_type (Γ_local ++ Γ) x.2) d_τs


  let βs := new_binders d_τs.length

  let (Γ_cτs, Γ_ty) := Γ_local.partition (λ x => x.is_type)

  let eqs := mk_eqs (List.zip d_τs_kis (List.zip βs (List.map (λ x => [P' Γ_cτs.length][S' βs.length] x.snd) d_τs)))


  let ty' := [S' (eqs.length + Γ_local.length)] mk_ty_apps ([S' βs.length]#d) βs

  let Γ_cτs' := Γ_cτs.map (λ x => x.apply (S' (βs.length + eqs.length)))

  let Γ' := Γ_cτs' ++ mk_type_telescope (mk_kind_telescope Γ_ty d_τs_kis) eqs

  -- let ty' := ty'.from_telescope_rev Γ_cτs'

  let ty' := ty'.from_telescope_rev Γ'

  .some ty'

def mk_inst_type : Ctx Term -> List Nat -> Term -> List Term -> Term := λ Γ βs C ics => `0


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
  let ty_vars := new_binders args_k.length


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
  let ity' <- hf_encode Γ' ity'

  let Γ' := .insttype ity' :: Γ'


  -- let k'' <- compile Γ' □ k'
  -- let (_ , res_τ) := C''.to_telescope
  -- let (h, _) <- res_τ.neutral_form


  -- Step2 : Check fundeps validity


  -- Step3 : compile openmethods


  .some Γ'
