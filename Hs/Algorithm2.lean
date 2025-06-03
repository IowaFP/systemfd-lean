import Hs.Algorithm

def new_binders_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => new_binders_aux n (#n :: acc)


def new_binders : Nat -> List Term := λ n => new_binders_aux n []
def re_index_base := new_binders

#eval new_binders 3

theorem new_binders_lemma : (new_binders n).length == n := by sorry

def mk_eqs : List (Term × Nat × Term) -> List Term := List.map (λ x => #x.2.1 ~[x.1]~ x.2.2)

def mk_kind_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@k a) h args

def mk_ty_apps : Term -> List Term -> Term := λ h args =>
  List.foldl (λ acc a => acc `@t a) h args

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
def hf_encode : Ctx Term -> Term -> Option Term := λ Γ x => do
  -- let (c_τs, res_ty) := x.to_telescope
  -- let (d, d_τs) <- res_ty.neutral_form

  -- let d_τs_kis := List.map (λ _ => `★) d_τs
  --   -- TODO: get the right kinds of d_τs but I don't know how to find the kind yet
  -- let βs := new_binders d_τs.length

  -- let eqs := mk_eqs (List.zip βs d_τs)

  -- let βs' := List.map (HsFrame.kind ·) βs
  -- let βs'' := (List.map (λ x => (HsSpineVariant.kind, (HsTerm.HsVar x))) βs)

  -- let res_ty' := d.apply_spine σs''

  -- -- separate τs from C τs as telescope returns all binders
  -- let (qty_vars, Cτs) := List.partition (·.is_kind) c_τs

  -- let c_τs' := List.map (λ x => (x.1, [S' σs.length] x.2)) c_τs
  -- let x' := res_ty'.apply_spine (σs'' ++ c_τs'))
  -- .some x'
  .none

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

| .cons (.classDecl C scs oms fds) Γ => do
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

  -- let class_ty := ([S' ty_vars_ctx.length] #0).from_telescope ty_varsctx -- indexed at Γ'


  let Γ' <- List.foldlM ( λ Γ sc_data => do -- TODO Fix Counting

    let cls_con := sc_data.1
    let sc := sc_data.2

    let class_type := mk_kind_apps ([S' ty_vars.length]cls_con) ty_vars
    let sc' <- compile Γ ★ sc

    let sc_fun : Term := .bind2 .arrow class_type sc'
    let sc_fun := sc_fun.from_telescope ty_vars_ctx

    .some (.openm sc_fun :: Γ)
    ) Γ' (List.zip (re_index_base scs.length) scs)


  -- let class_arity := ty_vars_ctx.length

  -- Step 3. Add fundeps



  -- Step 4. Add methods
  let Γ' <- List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .some ((.openm τ') :: Γ))
      Γ' oms

  -- and fd functions
  let fds' : Ctx Term := []
  .some Γ'

| .cons (.inst C ics mths) Γ => do -- TODO: instance constraints should be part of the instance type?
  let Γ'  <- compile_ctx Γ
  let C' <- compile Γ' □ C
  let ics' <- List.mapM (λ ic => compile Γ' ★ ic) ics
  let inst_type := mk_inst_type Γ' [] C' ics'
  let C'' <- hf_encode Γ' C'
  -- let k'' <- compile Γ' □ k'
  let (_ , res_τ) := C''.to_telescope
  let (h, _) <- res_τ.neutral_form

  .some (/-.inst (#h) sorry ::-/ .insttype C' :: Γ')
