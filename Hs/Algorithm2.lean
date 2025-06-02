import Hs.Algorithm


-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ τs. C τs -> D τs
-- and converts it to
-- ∀ σs τs. (σs ~ τs) -> C τs -> D σs

def hf_encode : HsTerm -> Option HsTerm := λ x => do
  let (τs, res_ty) := x.to_telescope

  let (d, d_τs) <- res_ty.neutral_form


  -- separate τs from C τs as telescope returns all binders
  let (qty_vars, Cτs) := List.partition
      (λ x => match x with
              | .kind _ => true
              | _ => false)
      τs



  .none



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
| .cons (.classDecl k _ oms _) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  let oms' <- List.mapM (compile Γ' ★ ·) oms
  let oms'' := List.map (λ x => Frame.openm x) oms'
  -- TODO: Compile scs and fds
  -- It amounts to producing the sc functions
  .some (/- scs' ++ fds ++ -/ oms'' ++ .opent k' :: Γ')
| .cons (.inst k ics mths) Γ => do -- TODO: instance constraints should be part of the instance type
  let Γ'  <- compile_ctx Γ
  let k' <- hf_encode k
  let k'' <- compile Γ' ★ k'
  let (_ , res_τ) := k''.to_telescope
  let (h, _) <- res_τ.neutral_form

  .some (/-.inst (#h) sorry ::-/ .insttype k'' :: Γ')
